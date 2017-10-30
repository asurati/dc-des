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
 * IK is Independent subKeys, where the subkeys are treated as mutually
 * independent and unrelated to the 56-bit DES key.
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

#define NT	16
#define NP	(NT >> 1)

static uint64_t g_k[4];

struct hextet {
	uint64_t ch[4];
	uint64_t pt[NT];

	/* [char][pair][ele]. */
	unsigned char pairs[4][NP][2];
};

struct dc4_ctx {
	struct hextet ht;
	uint64_t key;
	uint64_t ks[17];
};

static void gen_hextet(struct hextet *ht)
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

/* Bruteforce all keys for each sbox set in sbox_mask. */
/* The function should not memset sk to 0. */
static bool bf_sbox_key(struct sbox_key sk[8], const uint64_t cta[NT],
		 const struct dc4_ctx *c, int ch, uint32_t xor,
		 uint8_t sbox_mask)
{
	int i, j, k, x, y, z, l, ox;
	uint64_t se[NP][2];
	uint32_t oxor[NP];

	for (i = 0; i < NP; ++i) {
		/* Get the ct pair under the given characterstic. */
		x = c->ht.pairs[ch][i][0];
		y = c->ht.pairs[ch][i][1];

		/* right halves of the ciphertexts are the inputs.
		 * Expand them.
		 */
		se[i][0] = expand(cta[x]);
		se[i][1] = expand(cta[y]);

		oxor[i]  = cta[x] >> 32;
		oxor[i] ^= cta[y] >> 32;
		oxor[i] ^= xor;
		oxor[i]  = reverse_p(oxor[i]);
	}

	/* For each sbox S8 to S1. */
	for (i = 7; i >= 0; --i, sbox_mask >>= 1) {
		if ((sbox_mask & 1) == 0)
			continue;

		/* Current SBOX i = S(i+1). */
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
				x = sk[i].c;
				sk[i].keys[x] = j;
				++sk[i].c;
			}
		}

		/* For the current SBOX, no key was found, possibly due to
		 * incorrect ct. Return error. */
		if (sk[i].c == 0)
			return false;
	}

	return true;
}

static bool apply_char_k4(struct sbox_key sk[8], const uint64_t cta[NT],
		   const struct dc4_ctx *c, int ch)
{
	int i;
	uint8_t smask;
	uint64_t t;

	assert(ch == 0 || ch == 1);
	t = apply_ip(c->ht.ch[ch]);

	/* The characteristics chosen for the 4 round attack are such that, in
	 * round 2, the left half of the difference is the input to the round
	 * function.
	 */
	t = expand(t >> 32);
	smask = 0;
	for (i = 7; i >= 0; --i, t >>= 6) {
		/* Ignore any SBOX whose input difference is non-zero. */
		if (t & 0x3f)
			continue;
		smask |= 1 << (7 - i);
	}

	return bf_sbox_key(sk, cta, c, ch, 0, smask);
}

static bool apply_char_k3(struct sbox_key sk[8], const uint64_t cta[NT],
		   const struct dc4_ctx *c, int ch)
{
	uint64_t t;

	assert(ch == 1);
	t = apply_ip(c->ht.ch[ch]);

	return bf_sbox_key(sk, cta, c, ch, t >> 32, 0xff);
}

static bool apply_char_k2(struct sbox_key sk[8], const uint64_t cta[NT],
		   const struct dc4_ctx *c, int ch)
{
	uint64_t t;

	t = apply_ip(c->ht.ch[ch]);

	return bf_sbox_key(sk, cta, c, ch, t, 0xff);
}

static bool apply_char_k1(struct sbox_key sk[8], const uint64_t cta[NT],
		   const struct dc4_ctx *c, int ch)
{
	uint64_t t;

	t = apply_ip(c->ht.ch[ch]);

	return bf_sbox_key(sk, cta, c, ch, t >> 32, 0xff);
}

static void peel(uint64_t ctc[NT], const uint64_t cta[NT], uint64_t key)
{
	int i;
	uint64_t ct;
	uint32_t lco, rco, lci, rci, lpo, rpo;

	for (i = 0; i < NT; ++i) {
		ct = cta[i];

		lco = ct >> 32;
		rco = ct;

		lci = lco ^ desf(rco, key);
		rci = rco;

		lpo = rci;
		rpo = lci;

		ct = lpo;
		ct <<= 32;
		ct |= rpo;

		ctc[i] = ct;
	}
}

static bool find_k1(const uint64_t cta[NT], const struct dc4_ctx *c)
{
	bool bret, found;
	int i, ki[8], ch, x, y;
	uint64_t t;
	uint64_t ctc[NT];
	struct sbox_key sk[8];

	memset(sk, 0, sizeof(sk));
	memset(ki, 0xff, sizeof(ki));

	if (!apply_char_k1(sk, cta, c, 3))
		return false;

	found = false;

	while (1) {
		g_k[0] = next_subkey(ki, sk);
		if (g_k[0] == (uint64_t)-1)
			break;
		peel(ctc, cta, g_k[0]);

		/* The reversal performed in peel needs to be undone for the
		 * first round. Reverse again to undo.
		 */
		for (i = 0; i < NT; ++i)
			ctc[i] = ((ctc[i] & 0xfffffffful) << 32) |
				(ctc[i] >> 32);

		/* ctc is the array of plaintexts (post IP). Select only those
		 * subkeys for which the plaintext difference matches the
		 * corresponding characteristics chosen.
		 */

		bret = true;
		for (ch = 0; ch < 4 && bret; ++ch) {
			for (i = 0; i < NP && bret; ++i) {
				x = c->ht.pairs[ch][i][0];
				y = c->ht.pairs[ch][i][1];
				t = ctc[x] ^ ctc[y];
				if (t != apply_ip(c->ht.ch[ch]))
					bret = false;
			}
		}

		/* Further reduce the set of possible subkeys by selecting only
		 * those under which the unmodified plaintext (i.e. the one
		 * with no charactersitic XOR'd) matches the corresponding
		 * decryption.
		 */
		if (bret && ctc[0] == apply_ip(c->ht.pt[0])) {
			found = true;
			printf("k1 %lx, k2 %lx, k3 %lx, k4 %lx\n",
			       g_k[0], g_k[1], g_k[2], g_k[3]);
		}
	}

	return found;
}

static bool find_k2(const uint64_t cta[NT], const struct dc4_ctx *c)
{
	bool found;
	int ki[8];
	uint64_t ctc[NT];
	struct sbox_key sk[8];

	memset(sk, 0, sizeof(sk));
	memset(ki, 0xff, sizeof(ki));

	if (!apply_char_k2(sk, cta, c, 2))
		return false;

	found = false;

	while (1) {
		g_k[1] = next_subkey(ki, sk);
		if (g_k[1] == (uint64_t)-1)
			break;
		peel(ctc, cta, g_k[1]);
		if (find_k1(ctc, c))
			found = true;
	}

	return found;
}

static bool find_k3(const uint64_t cta[NT], const struct dc4_ctx *c)
{
	bool found;
	int ki[8];
	uint64_t ctc[NT];
	struct sbox_key sk[8];

	memset(sk, 0, sizeof(sk));
	memset(ki, 0xff, sizeof(ki));

	/* If apply_char returns false, the subkey for the current + 1 round is
	 * likely to be incorrect, which might have resulted in the incorrect
	 * decryption/peel of the current + 1 round. Return to the current + 1
	 * round to try the next subkey at that round.
	 */
	if (!apply_char_k3(sk, cta, c, 1))
		return false;

	/* Found at least one valid subkey for the current round. Validity
	 * implies that subkey allowed correct decryptions at this and lower
	 * rounds. A correct decryption is detected when the pt is compared with
	 * the decryption at round 1.*/
	found = false;

	while (1) {
		g_k[2] = next_subkey(ki, sk);
		if (g_k[2] == (uint64_t)-1)
			break;
		peel(ctc, cta, g_k[2]);
		if (find_k2(ctc, c))
			found = true;
	}

	return found;
}

static void find_k4(const uint64_t cta[NT], const struct dc4_ctx *c)
{
	bool bret;
	int ki[8];
	uint64_t ctc[NT];
	struct sbox_key sk[8];

	memset(sk, 0, sizeof(sk));
	memset(ki, 0xff, sizeof(ki));

	bret = apply_char_k4(sk, cta, c, 0);
	assert(bret);

	bret = apply_char_k4(sk, cta, c, 1);
	assert(bret);

	/* It is required that, among the subkeys found for the last round,
	 * the target subkey be one of them.
	 */
	assert(contains(sk, c->ks[4]));

	bret = false;
	while (1) {
		g_k[3] = next_subkey(ki, sk);
		if (g_k[3] == (uint64_t)-1)
			break;
		peel(ctc, cta, g_k[3]);

		if (find_k3(ctc, c))
			bret = true;
	}

	/* If a set of valid subkeys are not found, fire the assert. */
	assert(bret);
}

int main()
{
	int i;
	uint64_t cta[NT];
	struct dc4_ctx c;
	/* Fix a temporary key while work-in-progress. */
	uint8_t key[8] = {
		0x9a,0x8c,0xe6,0x3a,0x60,0xf4,0xde,0x36
	};

	memset(&c, 0, sizeof(c));

	/* Override the fixed key. */
	assert(getrandom(key, 8, 0) == 8);

	/* Seed the RNG used to generate the plaintext bytes. */
	srand(time(NULL));

	c.key = htobe64(*(const uint64_t *)key);
	/* Zero the don't care bits within the key, for easier comparisons
	 * later.
	 */
	c.key &= ~DES_KEY_XCARE_MASK;

	/* We still generate the subkeys using the DES key schedule. Thus, the
	 * subkeys are not really independent. But during the attack, the
	 * reverse key schedule is not invoked, thus treating the subkeys as
	 * mutually independent and unrelated to the 56-bit DES key.
	 *
	 * The attack does compare the keys found with the keys generated, to
	 * ensure that a failure is flagged by the firing of asserts.
	 */
	ksa(c.ks, c.key);

	gen_hextet(&c.ht);
	for (i = 0; i < NT; ++i) {
		cta[i] = enc(c.ht.pt[i], c.ks, 4);
		/* Reverse the IPI effect of the enc. */
		cta[i] = apply_ip(cta[i]);
	}

	find_k4(cta, &c);
	return 0;
}
