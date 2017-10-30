/* Copyright (c) 2017 Amol Surati
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */


/* 6-Round-DES Differential Cryptanalysis through chosen-plaintext attacks.
 *
 * Based on the paper by Eli Biham and Adi Shamir.
 */

/* Assumes little-endian, LP64 model. */

#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/random.h>

#include "des.h"

#define NT	240
/* # of pairs per charactersitic. */
#define NP	(NT >> 1)
#define NQ	(NP >> 1)

/* A quartet, built from 2 characteristics, contains 2 pairs of both the
 * characteristics. Since 120 pairs of each characteristics suffice, 60 quartets
 * are needed.
 */

struct dc6_ctx {
	uint64_t seed;
	uint64_t ch[2];
	uint64_t pt[NT];
	uint64_t key;
	uint64_t ks[17];

	/* [char][pair][ele]. */
	uint8_t pairs[2][NP][2];
};

static int popcnt(uint64_t a)
{
	uint64_t b;
	asm volatile ("popcntq	%1, %0\n"
		      : "=r" (b)
		      : "r" (a));
	return b;
}

static int bsr(uint64_t a)
{
	uint64_t b;
	asm volatile ("bsrq	%1, %0\n"
		      : "=r" (b)
		      : "r" (a));
	return b;
}

static void gen_quartets(struct dc6_ctx *c)
{
	int i, j, k;
	uint64_t pt;
	uint8_t p[8];

	c->ch[0] = 0x801000004000ul;	/* IPI(Omega_1). */
	c->ch[1] = 0x80100100000ul;	/* IPI(Omega_2). */

	/* There are 60 quartets. Hence 60 random plaintexts. */
	for (i = 0; i < NQ; ++i) {
		for (j = 0; j < 8; ++j)
			p[j] = rand() & 0xff;
		j = i << 2;
		c->pt[j] = htobe64(*(const uint64_t *)p);
		c->pt[j + 1] = c->pt[j] ^ c->ch[0];
		c->pt[j + 2] = c->pt[j] ^ c->ch[1];
		c->pt[j + 3] = c->pt[j] ^ c->ch[0] ^ c->ch[1];

		/* Within each quartet, the pairs for ch0 are 0,1 and 2,3, and
		 * the pairs for ch1 are 0,2 and 1,3.
		 */
		k = i << 1;

		c->pairs[0][k][0] = j;
		c->pairs[0][k][1] = j + 1;
		c->pairs[1][k][0] = j;
		c->pairs[1][k][1] = j + 2;

		++k;
		c->pairs[0][k][0] = j + 2;
		c->pairs[0][k][1] = j + 3;
		c->pairs[1][k][0] = j + 1;
		c->pairs[1][k][1] = j + 3;
	}

	/* Verify the correctness of the pairs generated. */
	for (i = 0; i < 2; ++i) {
		for (j = 0; j < NP; ++j) {
			k = c->pairs[i][j][0];
			pt = c->pt[k];

			k = c->pairs[i][j][1];
			pt ^= c->pt[k];

			assert(pt == c->ch[i]);
		}
	}
}

static uint8_t bf_sbox_key(uint64_t km[NP][8], const uint64_t cta[NT],
			   const struct dc6_ctx *c, int ch)
{
	int i, j, k, x, y, z, ox;
	uint64_t t, se[NP][2];
	uint32_t oxor[NP];
	uint8_t smask;

	smask = 0;
	t = apply_ip(c->ch[ch]);

	/* F' = TL' ^ e' = TL' ^ c' ^ D'.
	 * D' for 5 SBOXes is 0. Hence for those SBOXes,
	 * F' = TL' ^ c', where c' == right half of the characteristic.
	 */
	for (i = 0; i < NP; ++i) {
		/* Get the ct pair under the given characterstic. */
		x = c->pairs[ch][i][0];
		y = c->pairs[ch][i][1];

		/* right halves of the ciphertexts are the inputs.
		 * Expand them.
		 */
		se[i][0] = expand(cta[x]);
		se[i][1] = expand(cta[y]);

		oxor[i]  = cta[x] >> 32;
		oxor[i] ^= cta[y] >> 32;
		oxor[i] ^= t;
		oxor[i]  = reverse_p(oxor[i]);
	}

	t = expand(t >> 32);
	/* For every pair, for every sbox with i/o difference == 0, for every
	 * key value, see if that key value results in the given output xor.
	 * If it does, mark the key value in the km.
	 */

	/* For each sbox S8 to S1. */
	for (i = 7; i >= 0; --i, t >>= 6) {
		/* Ignore any SBOX whose input difference is non-zero. */
		if (t & 0x3f) {
			smask |= 1 << (7 - i);
			continue;
		}

		/* Current SBOX i = S(i+1). */
		/* For each key 0 to 63. */
		for (j = 0; j < 64; ++j) {
			/* For each ct pair. */
			for (k = 0; k < NP; ++k) {
				/* Find the 4-bit output difference exiting
				 * the SBOX, for the current pair k.
				 */
				ox = oxor[k] >> ((7 - i) * 4);
				ox &= 0xf;

				/* Find the 6-bit input difference after the
				 * expansion but before the application of the
				 * key bits. Then XOR in the current key bits j.
				 *
				 * The result is a pair of inputs to the SBOX.
				 */
				x = ((se[k][0] >> (7 - i) * 6) & 0x3f) ^ j;
				y = ((se[k][1] >> (7 - i) * 6) & 0x3f) ^ j;

				/* Lookup the SBOX and calculate the output
				 * difference.
				 */
				z = sbox_lookup(i, x) ^ sbox_lookup(i, y);
				if (z != ox)
					continue;

				/* Set bit corresponding to key value j, inside
				 * the key mask for SBOX i for the pair k.
				 */
				km[k][i] |= 1ull << (63 - j);
			}
		}
	}

	return smask;
}

struct stack_entry {
	int ix;
	uint64_t res[8];
} stack[NP];

/* Find a largest possible set of pairs all of which suggest
 * some common key value.
 */
static bool find_pairs_set(uint64_t res[8], const uint64_t km[NP][8],
			   uint8_t smask)
{
	bool found;
	int i, j, l;
	int tos, max_tos;

	tos = max_tos = -1;
	found = false;

	l = 1;
	++tos;
	stack[tos].ix = 0;
	memcpy(stack[tos].res, km[0], 8 * sizeof(uint64_t));

	while (1) {
		assert(tos < NP);
		/* Get the TOS result and ix, and find the next element which
		 * results in a nonzero AND.
		 */
		for (i = stack[tos].ix + l; i < NP; ++i) {
			for (j = 0; j < 8; ++j) {
				if (smask & (1 << (7 - j)))
					continue;
				if (stack[tos].res[j] & km[i][j])
					continue;
				break;
			}
			if (j == 8)
				break;
		}

		if (i != NP) {
			/* Found i which can be pushed into the stack. */
			l = 1;
			++tos;
			assert(tos > 0);
			stack[tos].ix = i;
			memcpy(stack[tos].res, stack[tos - 1].res,
			       8 * sizeof(uint64_t));
			for (j = 0; j < 8; ++j)
				stack[tos].res[j] &= km[i][j];

			if (tos > max_tos) {
				max_tos = tos;
			} else	if (tos < max_tos) {
				continue;
			}

			/* Skip results which list multiple keys for any
			 * SBOX.
			 */
			for (i = 0; i < 8; ++i)
				if (popcnt(stack[tos].res[i]) > 1)
					break;
			/* Found a set of pairs which suggests a single result
			 * for each of the (considered) SBOX. Save in the output
			 * buffer.
			 */
			if (i == 8) {
				memcpy(res, stack[tos].res,
				       8 * sizeof(uint64_t));
				found = true;
			}
		} else {
			if (tos > 0) {
				l = stack[tos].ix - stack[tos - 1].ix + 1;
				--tos;
			} else {
				l = 1;
				i = stack[tos].ix + 1;
				if (i == NP)
					break;
				memcpy(stack[tos].res, km[i], 8 * sizeof(uint64_t));
				stack[tos].ix = i;
			}
		}
	}

	return found;
}

static void find_key(const uint64_t cta[NT], const struct dc6_ctx *c)
{
	int i, ki[8];
	uint64_t km[NP][8], res[2][8], mask, key, ck, pt;
	uint8_t smask[2];
	uint64_t ks[17];
	struct sbox_key sk[8];

	/*
	 *0:      s2       s5 s6 s7 s8
	 *1:   s1 s2    s4 s5 s6
	 *
	 */

	memset(res, 0xff, sizeof(res));

	/* Apply Omega1. */
	memset(km, 0, sizeof(km));
	smask[0] = bf_sbox_key(km, cta, c, 0);
	assert(find_pairs_set(res[0], km, smask[0]));

	/* Apply Omega2. */
	memset(km, 0, sizeof(km));
	smask[1] = bf_sbox_key(km, cta, c, 1);
	assert(find_pairs_set(res[1], km, smask[1]));

	/* Setup the possible subkeys for each SBOX. */

	/* S3 is unknown. */
	sk[2].c = 1;
	sk[2].keys[0] = 0;

	/* S1. */
	sk[0].c = 1;
	sk[0].keys[0] = 0x3f - bsr(res[1][0]);

	/* S4. */
	sk[3].c = 1;
	sk[3].keys[0] = 0x3f - bsr(res[1][3]);

	/* S7. */
	sk[6].c = 1;
	sk[6].keys[0] = 0x3f - bsr(res[0][6]);

	/* S8. */
	sk[7].c = 1;
	sk[7].keys[0] = 0x3f - bsr(res[0][7]);

	/* S2. */
	sk[1].c = 1;
	sk[1].keys[0] = 0x3f - bsr(res[0][1]);
	if (res[0][1] != res[1][1]) {
		sk[1].c = 2;
		sk[1].keys[1] = 0x3f - bsr(res[1][1]);
	}

	/* S5. */
	sk[4].c = 1;
	sk[4].keys[0] = 0x3f - bsr(res[0][4]);
	if (res[0][4] != res[1][4]) {
		sk[4].c = 2;
		sk[4].keys[1] = 0x3f - bsr(res[1][4]);
	}

	/* S6. */
	sk[5].c = 1;
	sk[5].keys[0] = 0x3f - bsr(res[0][5]);
	if (res[0][5] != res[1][5]) {
		sk[5].c = 2;
		sk[5].keys[1] = 0x3f - bsr(res[1][5]);
	}

	memset(ki, 0xff, sizeof(ki));
	while (1) {
		key = next_subkey(ki, sk);
		if (key == (uint64_t)-1)
			break;
		/* S3 is not available. Bruteforce. */
		mask = 0xfc0000000ul;
		reverse_ksa(&key, &mask, 6);
		for (i = 0; i < (1 << 14); ++i) {
			ck = apply_mask(key, mask, i, 14);
			ksa(ks, ck);
			pt = dec(apply_ipi(cta[0]), ks, 6);
			if (pt == c->pt[0]) {
				printf("ck %lx\n", ck);
				assert(ck == c->key);
				return;
			}
		}
	}

	/* Seed 0x59f6e4a2 forces the computation here. */
	printf("Original subkey: %lx\n", c->ks[6]);
	printf("Calculated subkeys (with S3_k set to 0):\n");
	memset(ki, 0xff, sizeof(ki));
	while (1) {
		key = next_subkey(ki, sk);
		if (key == (uint64_t)-1)
			break;
		printf("%lx\n", key);
	}
	printf("Retry with a different plaintext generator seed.\n");
}

int main()
{
	int i;
	uint64_t cta[NT];
	struct dc6_ctx c;
	uint8_t key[8] = {
		0x9a,0x8c,0xe6,0x3a,0x60,0xf4,0xde,0x36
	};

	memset(&c, 0, sizeof(c));

	/* Override the fixed key. */
	//assert(getrandom(key, 8, 0) == 8);

	/* Seed the RNG used to generate the plaintext bytes. */
	c.seed = time(NULL);
	srand(c.seed);
	printf("seed %lx\n", c.seed);

	c.key = htobe64(*(const uint64_t *)key);
	/* Zero the don't care bits within the key, for easier comparisons
	 * later.
	 */
	c.key &= ~DES_KEY_XCARE_MASK;

	ksa(c.ks, c.key);

	gen_quartets(&c);
	for (i = 0; i < NT; ++i) {
		cta[i] = enc(c.pt[i], c.ks, 6);
		/* Reverse the IPI effect of the enc. */
		cta[i] = apply_ip(cta[i]);
	}

	find_key(cta, &c);

	return 0;
}
