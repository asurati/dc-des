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


/* 4-Round-DES-IK Differential Cryptanalysis through chosen-plaintext attacks.
 * IK is Independent subKeys, where the subkeys of each round are treated as
 * mutually independent.
 *
 * Based on the paper by Eli Biham and Adi Shamir.
 */

/* Assumes little-endian, LP64 model. */

#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/random.h>

#include "des.h"

#define NT	16
#define NP	(NT >> 1)

struct hextet {
	uint64_t ch[4];
	uint64_t pt[NT];
	uint64_t ct[NT];

	/* [char][pair][ele]. */
	unsigned char pairs[4][NP][2];
};

struct dc4_ctx {
	struct hextet ht;
	uint64_t key;
	uint64_t seed;
};

void gen_hextet(struct hextet *ht)
{
	int i, j, k;
	int c[4], ch;
	uint64_t pt;
	uint8_t p[8];

	ht->ch[0] = 0x400000ul;	/* IPI(Omega_1). */
	ht->ch[1] = 0x55000000150000ul;	/* IPI(Omega_2). */

	/* In the first round, for all SBOXes,
	 * - the input difference after expansion must not be zero,
	 * - the input difference after expansion from P3 is different than that
	 *   from P4.
	 */

	ht->ch[2] = 0xaaa0220aa2208828ul;
	ht->ch[3] = 0xa8a2a22028088808ul;
	/* These values provide:
	 * input XORs after IP: 53b7c91d 471ff106
	 * input XORs after IP and expansion: aa7dafe528fa 20e8fffa280c
	 */

	for (i = 0; i < 8; ++i)
		p[i] = rand() & 0xff;
	pt = htobe64(*(const uint64_t *)p);

	/* XOR the corresponding characteristics with pt. */
	for (i = 0; i < NT; ++i) {
		ht->pt[i] = pt;
		/* ch0. */
		if (i & 8)
			ht->pt[i] ^= ht->ch[0];
		/* ch1. */
		if (i & 4)
			ht->pt[i] ^= ht->ch[1];
		/* ch2. */
		if (i & 2)
			ht->pt[i] ^= ht->ch[2];
		/* ch3. */
		if (i & 1)
			ht->pt[i] ^= ht->ch[3];
	}

	memset(c, 0, sizeof(c));
	for (i = 0; i < NT; ++i) {
		for (j = i + 1; j < NT; ++j) {
			k = i ^ j;

			if (k == 8)
				ch = 0;
			else if (k == 4)
				ch = 1;
			else if (k == 2)
				ch = 2;
			else if (k == 1)
				ch = 3;
			else
				continue;

			ht->pairs[ch][c[ch]][0] = i;
			ht->pairs[ch][c[ch]][1] = j;
			++c[ch];
		}
	}

	/* Verify the correctness of the pairs generated. */
	for (i = 0; i < 4; ++i) {
		for (j = 0; j < NP; ++j) {
			k = ht->pairs[i][j][0];
			pt = ht->pt[k];

			k = ht->pairs[i][j][1];
			pt ^= ht->pt[k];

			assert(pt == ht->ch[i]);
		}
	}
}

uint64_t apply_char(const struct dc4_ctx *c, int ch)
{
	int i, j, k, x, y, z, m, l, ox;
	uint32_t oxor[NP];
	uint64_t se[NP][2], t, key;
	uint64_t ct[NP][2], mask;

	assert(ch == 0 || ch == 1);

	for (i = 0; i < NP; ++i) {
		/* Get the ct pair under the given characterstic. */
		x = c->ht.pairs[ch][i][0];
		y = c->ht.pairs[ch][i][1];
		ct[i][0] = c->ht.ct[x];
		ct[i][1] = c->ht.ct[y];

		/* IPI(-1) = IP of the CT pair contains the input to the
		 * 4th round. */
		ct[i][0] = apply_ip(ct[i][0]);
		ct[i][1] = apply_ip(ct[i][1]);

		/* right halves of the ciphertexts are the inputs.
		 * Expand them.
		 */
		se[i][0] = expand(ct[i][0]);
		se[i][1] = expand(ct[i][1]);

		/* D' = B' ^ l'. Calculate D'. Those SBOXes for which the output
		 * difference B' has 0, have their key bits exposed.
		 */
		oxor[i]  = ct[i][0] >> 32;
		oxor[i] ^= ct[i][1] >> 32;
		oxor[i]  = reverse_p(oxor[i]);
	}

	t = apply_ip(c->ht.ch[ch]);

	/* The characteristics chosen for the 4 round attack are such that, in
	 * round 2, the left half of the difference is the input to the round
	 * function.
	 */
	t = expand(t >> 32);
	key = 0;
	mask = 0;
	/* For each sbox S8 to S1. */
	for (i = 7; i >= 0; --i, t >>= 6) {
		/* Ignore any SBOX whose input difference is not zero. */
		if (t & 0x3f) {
			/* Set the mask of the unknown key bits. */
			mask |= 0x3ful << ((7 - i) * 6);
			continue;
		}
		/* Current SBOX i = S(i+1). */
		m = -1;
		/* For each key 0 to 63. */
		for (j = 0; j < 64; ++j) {
			l = 0;
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

				/* If j is the correct key entering the SBOX,
				 * *all* pairs will force the condition below to
				 * satisfy. i.e. the count at the end of this
				 * loop must be equal to NP, for the correct key.
				 */
				if (z == ox)
					++l;
			}

			if (l == NP) {
				/* Increase NP, and compile and run again, if
				 * the assert fires, i.e. if we find multiple
				 * candidate 6-bit key for the SBOX.
				 */
				if (m != -1) {
					printf("multiple subkeys for sbox %d\n",
					       i + 1);
					/* The seed and the key are all one
					 * needs to recreate the rare situation.
					 */
					printf("seed %lx, key %lx\n", c->seed,
					       c->key);
				}

				assert(m == -1);

				/* Save the key bits entering the SBOX. */
				m = j;
			}
		}

		assert(m != -1);
		key |= ((uint64_t)m << (7 - i) * 6);
	}

	return key;
}

void find_k4(const struct dc4_ctx *c, int nr)
{
	uint64_t k4;
	k4  = apply_char(c, 0);
	k4 |= apply_char(c, 1);

	/* TODO 'Peel off' the effect of the 4th round and apply the 2nd
	 * characteristic (ch1) to the 3 round cryptosystem to recover k3.
	 */

	/* Not yet complete. */
}

#if 0
void find_key(const struct dc4_ctx *c, int nr)
{
	int i, j, k, l, m;
	int ox;
	uint64_t ct[NP][2], ck;
	uint64_t pt0, pt1, ks[17];
	uint32_t oxor[NP];
	uint64_t se[NP][2], k4, key;

	uint64_t mask;

	/* k4 does not contain the key bits for S1. Create and trace a mask
	 * of the unknown bits, which are later found using bruteforce.
	 */
	mask = 0xfc0000000000ul;
	key = k4;

	reverse_ksa(&key, &mask, nr);
	/* mask must have 14 bits set - 6 unknown bits, which enter S1 in
	 * round 4, and the 8 missing bits due to reverse PC2.
	 */

	/* Bruteforce. */
	for (i = 0; i < (1 << 14); ++i) {
		ck = apply_mask(key, mask, i, 14);
		ksa(ks, ck);
		for (j = 0; j < NP; ++j) {
			pt0 = dec(c->ct[j][0], ks, nr);
			pt1 = dec(c->ct[j][1], ks, nr);
			if ((pt0 ^ pt1) != c->ixor)
				break;
		}

		if (j == NP) {
			pt0 = dec(c->ct[0][0], ks, nr);
			if (c->pt == pt0) {
				assert(ck == c->key);
				printf("ck %lx\n", ck);
			}
			/*
			for (j = 0; j < NP; ++j) {
				pt0 = dec(c->ct[j][0], ks, nr);
				pt1 = dec(c->ct[j][1], ks, nr);
				assert((pt0 ^ pt1) == c->ixor);
			}
			*/
		}
	}

	/* If the only check made during the bruteforce procedure is on
	 * plaintext difference, then there are 4 related keys which emerge (one
	 * of them is indeed the target key).
	 *
	 * If the target key is labelled key0, then the 3 other keys are related
	 * to it in the following manner:
	 *
	 * key1 = key0 ^ 0x00000010000000
	 * key2 = key0 ^ 0x40000000000000
	 * key3 = key0 ^ 0x40000010000000
	 *
	 * These 4 keys are indistinguishable when looking only at the plaintext
	 * differences. Comparing the plaintexts themselves (original plaintext
	 * generated when the attack began, and the plaintext generated by the
	 * decryption above) does list a single key (the target key) as the
	 * result.
	 *
	 * TODO: Investigate the reason for such a relation between the
	 * particular plaintext difference and the 4 keys.
	 *
	 * See http://krypto.netlify.com for some description.
	 */


	/* In this particular attack, the 6 key bits of S1 were bruteforced.
	 * An alternative could be to select another set of 16 plaintexts with
	 * the characteristic 0x0222222200000000 (also from the paper) and to
	 * use the same method as implemented here on them. A complete k4 subkey
	 * then becomes available and only 8 remaining bits need to be
	 * discovered.
	 */
}
#endif

int main()
{
	int i;
	struct dc4_ctx c;
	uint64_t ks[17];
	/* Fix a temporary key while work-in-progress. */
	uint8_t key[8] = {
		0x9a,0x8c,0xe6,0x3a,0x60,0xf4,0xde,0x36
	};

	memset(&c, 0, sizeof(c));

	c.seed = time(NULL);
	srand(c.seed);

	c.key = htobe64(*(const uint64_t *)key);
	/* Zero the don't care bits within the key, for easier comparisons
	 * later.
	 */
	c.key &= ~DES_KEY_XCARE_MASK;

	/* We still generate the subkeys using the DES key schedule. Thus the
	 * subkeys are not really independent. But during the attack, the
	 * reverse key schedule is not invoked, thus treating the subkeys as
	 * independent.
	 */
	ksa(ks, c.key);

	gen_hextet(&c.ht);
	for (i = 0; i < NT; ++i)
		c.ht.ct[i] = enc(c.ht.pt[i], ks, 4);

	find_k4(&c, 4);
	return 0;
}
