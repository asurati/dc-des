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


/* 4-Round-DES Differential Cryptanalysis through chosen-plaintext attacks.
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

#define NP 16

struct dc4_ctx {
	uint64_t pt;
	uint64_t ct[NP][2];
	uint64_t key, ixor;
};

void find_key(const struct dc4_ctx *c, int nr)
{
	int i, j, k, l, m;
	int ox;
	uint64_t ct[NP][2], ck;
	uint64_t pt0, pt1, ks[17];
	uint32_t oxor[NP];
	uint64_t se[NP][2], k4, key;

	uint64_t mask;

	for (i = 0; i < NP; ++i) {
		/* IPI(-1) = IP of the CT pair contains the input to the
		 * 4th round. */
		ct[i][0] = apply_ip(c->ct[i][0]);
		ct[i][1] = apply_ip(c->ct[i][1]);

		/* right halves of the ciphertexts are the input.
		 * Expand them.
		 */
		se[i][0] = expand(ct[i][0]);
		se[i][1] = expand(ct[i][1]);

		/* D' = B' ^ l'. Calculate l'. The 28 output bits of B',
		 * corresponding to the outputs of S2..S8 in round 1, are 0.
		 * Thus the calculation provides the 28 output bits of D',
		 * corresponding to the outputs of S2..S8 in round 4.
		 * The outputs here are the output differences.
		 */
		oxor[i] = ct[i][0] >> 32;
		oxor[i] ^= ct[i][1] >> 32;
		oxor[i] = reverse_p(oxor[i]);
	}

	/* Work on the 28 available bits of the output difference and 48 (all)
	 * available bits of the input, to determine the 42 bits of k4,
	 * corresponding to the key bits entering S2..S8.
	 *
	 * For each SBOX and for each possible key entering that SBOX, calculate
	 * the number of ciphertext pairs which are consistent with the
	 * calculated input and output difference values.
	 */

	k4 = 0;

	/* For each sbox S8 to S2. */
	for (i = 7; i > 0; --i) {
		/* Current SBOX i = S(i+1). */
		m = -1;
		/* For each key 0 to 63. */
		for (j = 0; j < 64; ++j) {
			l = 0;
			/* For each ct pair. */
			for (k = 0; k < NP; ++k) {
				char x, y, z;

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
				assert(m == -1);

				/* Save the key bits entering the SBOX. */
				m = j;
			}
		}

		assert(m != -1);
		k4 |= ((uint64_t)m << (7 - i) * 6);
	}

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
	 */
}

int main()
{
	int i, j;
	struct dc4_ctx c;
	uint64_t ks[17];
	uint64_t xor, pt0, pt1;
	uint8_t key[8];
	uint8_t p[8];

	memset(&c, 0, sizeof(c));

	assert(getrandom(key, 8, 0) == 8);
	srand(time(NULL));

	c.key = htobe64(*(const uint64_t *)key);
	/* Zero the don't care bits within the key, for easier comparisons
	 * later.
	 */
	c.key &= ~DES_KEY_XCARE_MASK;
	ksa(ks, c.key);

	/* xor = L' */
	xor = 0x2000000000000000ul;
	/* xor = xor of the plaintext pre IP. */
	xor = apply_ipi(xor);
	c.ixor = xor;
	for (i = 0; i < NP; ++i) {
		for (j = 0; j < 8; ++j)
			p[j] = rand() & 0xff;

		pt0 = htobe64(*(const uint64_t *)p);
		pt1 = pt0 ^ xor;

		/* Save the first plaintext for later comparison. */
		if (i == 0)
			c.pt = pt0;
		c.ct[i][0] = enc(pt0, ks, 4);
		c.ct[i][1] = enc(pt1, ks, 4);
	}
	find_key(&c, 4);
	return 0;
}
