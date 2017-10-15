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


/* 3-Round-DES Differential Cryptanalysis through chosen-plaintext attacks.
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

struct dc3_ctx {
	uint64_t ct[2];
	uint64_t pt[2];
	char sk[8][64];
	int skc[8];
	uint64_t k3;
	uint64_t key;
};

char find_k3(struct dc3_ctx *c)
{
	int i, j, k;
	int ix, ox;
	uint64_t ixor, se[2];
	uint32_t oxor;
	char sk[64], rsk[64];
	int skc, rskc;

	/* IP on PT and IPI^(-1) = IP on CT. */
	c->pt[0] = apply_ip(c->pt[0]);
	c->pt[1] = apply_ip(c->pt[1]);
	c->ct[0] = apply_ip(c->ct[0]);
	c->ct[1] = apply_ip(c->ct[1]);

	/* right halves of the plaintexts post IP should be equal. */
	assert((uint32_t)c->pt[0] == (uint32_t)c->pt[1]);

	/* right halves of the ciphertexts are the input to the round
	 * function. Expand them into 48 bits.
	 */
	se[0] = expand(c->ct[0]);
	se[1] = expand(c->ct[1]);
	ixor  = se[0] ^ se[1];

	/* left halves of the ciphertexts and the plaintexts (total 4 values)
	 * XORed together is the output xor, but with the perm P applied.
	 */
	oxor  = c->pt[0] >> 32;
	oxor ^= c->pt[1] >> 32;
	oxor ^= c->ct[0] >> 32;
	oxor ^= c->ct[1] >> 32;

	/* Reverse the perm P. */
	oxor = reverse_p(oxor);

	for (i = 7; i >= 0; --i) {
		ix = ixor & 0x3f;
		ox = oxor & 0xf;

		skc = pxt_count(i, ix, ox);
		for (j = 0; j < skc; ++j) {
			sk[j] = pxt_value(i, ix, ox, j) ^ (se[0] & 0x3f);
		}

		if (c->skc[i] == 0) {
			memcpy(c->sk[i], sk, skc);
			c->skc[i] = skc;
		} else {
			/* Intersect. */
			rskc = 0;
			for (j = 0; j < skc; ++j) {
				for (k = 0; k < c->skc[i]; ++k) {
					if (sk[j] != c->sk[i][k])
						continue;
					rsk[rskc++] = sk[j];
				}
			}
			memcpy(c->sk[i], rsk, rskc);
			c->skc[i] = rskc;
			assert(rskc);
		}
		se[0] >>= 6;
		ixor >>= 6;
		oxor >>= 4;
	}

	/* If the S_K choices for each SBOX are reduced to 1, k3 is found.
	 */
	for (i = 7; i >= 0; --i)
		if (c->skc[i] != 1)
			break;

	if (i >= 0)
		return 0;

	c->k3 = 0;
	for (i = 0; i < 8; ++i) {
		c->k3 <<= 6;
		assert(c->skc[i] == 1);
		c->k3 |= c->sk[i][0];
	}

	/* k3 found. */
	return 1;
}

void find_key(struct dc3_ctx *c, int nr)
{
	int i, j;
	uint64_t ks[17];
	uint64_t ct[2];
	uint64_t key, mask, ck;
	uint32_t cc[2], dd[2];
	uint8_t shifts[17] = {
		0, /* unused. */
		1,1,2,2,2,2,2,2,
		1,2,2,2,2,2,2,1
	};
	uint8_t unk_bits_pc2[] = {
		 9,18,22,25,35,38,43,54
	};

	key = reverse_pc2(c->k3);

	/* k3 (48 bits) to c3d3 (56 bits) cannot provide the values for
	 * unk_bits positions. Create and trace a mask of these unknown bits.
	 */
	mask = 0;
	for (i = 0; i < 8; ++i) {
		j = unk_bits_pc2[i] - 1;
		mask |= 1ul << (55 - j);
	}

	/* Perform the reversal of the shifts on the mask. It provides the
	 * mask of the unknown bits in c0d0.
	 * Perform the reversal of the shifts on the key. It provides c0d0.
	 */
	cc[0] = mask >> 28;
	dd[0] = mask & 0x0fffffff;
	cc[1] = key >> 28;
	dd[1] = key & 0x0fffffff;

	for (i = nr; i > 0; --i) {
		cc[0] = (cc[0] >> 1) | (cc[0] << 27);
		dd[0] = (dd[0] >> 1) | (dd[0] << 27);
		cc[1] = (cc[1] >> 1) | (cc[1] << 27);
		dd[1] = (dd[1] >> 1) | (dd[1] << 27);
		if (shifts[i] == 2) {
			cc[0] = (cc[0] >> 1) | (cc[0] << 27);
			dd[0] = (dd[0] >> 1) | (dd[0] << 27);
			cc[1] = (cc[1] >> 1) | (cc[1] << 27);
			dd[1] = (dd[1] >> 1) | (dd[1] << 27);
		}
		cc[0] &= 0x0fffffff;
		dd[0] &= 0x0fffffff;
		cc[1] &= 0x0fffffff;
		dd[1] &= 0x0fffffff;
	}

	/* We have c0d0 and the addresses of the unknown bits within c0d0.
	 */
	mask = cc[0];
	mask <<= 28;
	mask |= dd[0];

	key = cc[1];
	key <<= 28;
	key |= dd[1];

	/* Reverse pc1 on both the key and the mask. */
	mask = reverse_pc1(mask);
	key = reverse_pc1(key);

	/* The 56-bit key thus generated is missing 8 bits whose addresses
	 * are given by the mask. Bruteforce and test. */
	for (i = 0; i < 256; ++i) {
		ck = apply_mask(key, mask, i, 8);

		ksa(ks, ck);

		ct[0] = enc(c->pt[0], ks, nr);
		ct[1] = enc(c->pt[1], ks, nr);

		/* Compare the ciphertext (c->ct) generated under the target key
		 * with the ciphertext (ct) generated under the candidate key.
		 */
		if (memcmp(&ct[0], &c->ct[0], 8))
			continue;
		if (memcmp(&ct[1], &c->ct[1], 8))
			continue;

		/* Found. */
		break;
	}

	/* These asserts must not fire. */
	assert(i < 256);
	assert(ck == c->key);

	printf("key: %lx\n", ck);
}

int main()
{
	int i;
	char r;
	struct dc3_ctx c;
	uint64_t ks[17];
	uint64_t mask;
	uint8_t key[8];
	uint8_t p0[8];
	uint8_t p1[8];

	memset(&c, 0, sizeof(c));

	srand(time(NULL));
	gen_pairs_xor_tab();

	assert(getrandom(key, 8, 0) == 8);

	c.key = htobe64(*(const uint64_t *)key);
	/* Zero the don't care bits within the key, for easier comparisons
	 * later.
	 */
	c.key &= ~DES_KEY_XCARE_MASK;
	ksa(ks, c.key);

	/* The plaintext pair must be such that after IP, r0 of both the
	 * plaintexts are equal. The mask 0x00000000ffffffff has 1 on those
	 * addresses where the plaintexts (post IP processing) must be equal.
	 */

	/* Reverse IP on the mask, to tranform it into a mask which provides
	 * the addresses of the equal bits across the generated plaintext
	 * pair.
	 */
	mask = 0xfffffffful;
	mask = apply_ipi(mask);

	r = 0;
	while (r == 0) {
		/* Generate plaintext pairs. */
		for (i = 0; i < 8; ++i) {
			p0[i] = rand() & 0xff;
			p1[i] = rand() & 0xff;
		}

		c.pt[0] = htobe64(*(const uint64_t *)p0);
		c.pt[1] = htobe64(*(const uint64_t *)p1);

		/* mask has 1 set for bit-addresses whose bit values must be
		 * equal in both the plaintexts. Adjust pt[1] to comply.
		*/
		c.pt[1] &= ~mask;
		c.pt[1] |= mask & c.pt[0];

		c.ct[0] = enc(c.pt[0], ks, 3);
		c.ct[1] = enc(c.pt[1], ks, 3);

		/* Overwrites ct and pt. */
		r = find_k3(&c);
	}

	/* Use any available pt-ct pair generated under the target key. */
	c.pt[0] = htobe64(*(const uint64_t *)p0);
	c.pt[1] = htobe64(*(const uint64_t *)p1);

	c.ct[0] = enc(c.pt[0], ks, 3);
	c.ct[1] = enc(c.pt[1], ks, 3);

	find_key(&c, 3);

	return 0;
}
