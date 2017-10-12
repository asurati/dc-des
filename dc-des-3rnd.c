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

const uint8_t pc1[56] = {
	57,49,41,33,25,17,9,
	1,58,50,42,34,26,18,
	10,2,59,51,43,35,27,
	19,11,3,60,52,44,36,
	63,55,47,39,31,23,15,
	7,62,54,46,38,30,22,
	14,6,61,53,45,37,29,
	21,13,5,28,20,12,4,
};

const uint8_t pc2[48] = {
	14,17,11,24,1,5,
	3,28,15,6,21,10,
	23,19,12,4,26,8,
	16,7,27,20,13,2,
	41,52,31,37,47,55,
	30,40,51,45,33,48,
	44,49,39,56,34,53,
	46,42,50,36,29,32,
};

const uint8_t ip[64] = {
	58,50,42,34,26,18,10,2,
	60,52,44,36,28,20,12,4,
	62,54,46,38,30,22,14,6,
	64,56,48,40,32,24,16,8,
	57,49,41,33,25,17,9,1,
	59,51,43,35,27,19,11,3,
	61,53,45,37,29,21,13,5,
	63,55,47,39,31,23,15,7,
};

const uint8_t ipi[64] = {
	40,8,48,16,56,24,64,32,
	39,7,47,15,55,23,63,31,
	38,6,46,14,54,22,62,30,
	37,5,45,13,53,21,61,29,
	36,4,44,12,52,20,60,28,
	35,3,43,11,51,19,59,27,
	34,2,42,10,50,18,58,26,
	33,1,41,9,49,17,57,25,
};

const uint8_t etab[48] = {
	32,1,2,3,4,5,
	4,5,6,7,8,9,
	8,9,10,11,12,13,
	12,13,14,15,16,17,
	16,17,18,19,20,21,
	20,21,22,23,24,25,
	24,25,26,27,28,29,
	28,29,30,31,32,1
};

const uint8_t fp[32] = {
	16,7,20,21,
	29,12,28,17,
	1,15,23,26,
	5,18,31,10,
	2,8,24,14,
	32,27,3,9,
	19,13,30,6,
	22,11,4,25,
};

const uint8_t sbox[8][64] = {
	{
		14,4,13,1,2,15,11,8,3,10,6,12,5,9,0,7,
		0,15,7,4,14,2,13,1,10,6,12,11,9,5,3,8,
		4,1,14,8,13,6,2,11,15,12,9,7,3,10,5,0,
		15,12,8,2,4,9,1,7,5,11,3,14,10,0,6,13
	},
	{
		15,1,8,14,6,11,3,4,9,7,2,13,12,0,5,10,
		3,13,4,7,15,2,8,14,12,0,1,10,6,9,11,5,
		0,14,7,11,10,4,13,1,5,8,12,6,9,3,2,15,
		13,8,10,1,3,15,4,2,11,6,7,12,0,5,14,9
	},
	{
		10,0,9,14,6,3,15,5,1,13,12,7,11,4,2,8,
		13,7,0,9,3,4,6,10,2,8,5,14,12,11,15,1,
		13,6,4,9,8,15,3,0,11,1,2,12,5,10,14,7,
		1,10,13,0,6,9,8,7,4,15,14,3,11,5,2,12
	},
	{
		7,13,14,3,0,6,9,10,1,2,8,5,11,12,4,15,
		13,8,11,5,6,15,0,3,4,7,2,12,1,10,14,9,
		10,6,9,0,12,11,7,13,15,1,3,14,5,2,8,4,
		3,15,0,6,10,1,13,8,9,4,5,11,12,7,2,14
	},
	{
		2,12,4,1,7,10,11,6,8,5,3,15,13,0,14,9,
		14,11,2,12,4,7,13,1,5,0,15,10,3,9,8,6,
		4,2,1,11,10,13,7,8,15,9,12,5,6,3,0,14,
		11,8,12,7,1,14,2,13,6,15,0,9,10,4,5,3
	},
	{
		12,1,10,15,9,2,6,8,0,13,3,4,14,7,5,11,
		10,15,4,2,7,12,9,5,6,1,13,14,0,11,3,8,
		9,14,15,5,2,8,12,3,7,0,4,10,1,13,11,6,
		4,3,2,12,9,5,15,10,11,14,1,7,6,0,8,13
	},
	{
		4,11,2,14,15,0,8,13,3,12,9,7,5,10,6,1,
		13,0,11,7,4,9,1,10,14,3,5,12,2,15,8,6,
		1,4,11,13,12,3,7,14,10,15,6,8,0,5,9,2,
		6,11,13,8,1,4,10,7,9,5,0,15,14,2,3,12
	},
	{
		13,2,8,4,6,15,11,1,10,9,3,14,5,0,12,7,
		1,15,13,8,10,3,7,4,12,5,6,11,0,14,9,2,
		7,11,4,1,9,12,14,2,0,6,10,13,15,3,5,8,
		2,1,14,7,4,10,8,13,15,12,9,0,3,5,6,11
	}
};

/* Don't care bits within a 64-bit key. */
uint8_t xcare_bits[] = {
	8,16,24,32,40,48,56,64
};

uint64_t apply_ip(uint64_t a)
{
	int i, j;
	uint64_t b;
	b = 0;
	for (i = 0; i < 64; ++i) {
		j = ip[i] - 1;
		if (a & (1ul << (63 - j)))
			b |= 1ul << (63 - i);
	}
	return b;
}

uint64_t apply_ipi(uint64_t a)
{
	int i, j;
	uint64_t b;
	b = 0;
	for (i = 0; i < 64; ++i) {
		j = ipi[i] - 1;
		if (a & (1ul << (63 - j)))
			b |= 1ul << (63 - i);
	}
	return b;
}

uint64_t expand(uint32_t a)
{
	int i, j;
	uint64_t b;
	b = 0;
	for (i = 0; i < 48; ++i) {
		j = etab[i] - 1;
		if (a & (1 << (31 - j)))
			b |= 1ul << (47 - i);
	}
	return b;
}

uint32_t reverse_p(uint32_t a)
{
	int i, j;
	uint32_t b;
	b = 0;
	for (i = 0; i < 32; ++i) {
		j = fp[i] - 1;
		if (a & (1 << (31 - i)))
			b |= 1 << (31 - j);
	}
	return b;
}

uint32_t apply_p(uint32_t a)
{
	int i, j;
	uint32_t b;
	b = 0;
	for (i = 0; i < 32; ++i) {
		j = fp[i] - 1;
		if (a & (1 << (31 - j)))
			b |= 1 << (31 - i);
	}
	return b;
}

/* Input 64 bits, Output 56 bits. */
uint64_t apply_pc1(uint64_t a)
{
	int i, j;
	uint64_t b;

	b = 0;
	for (i = 0; i < 56; ++i) {
		j = pc1[i] - 1;
		if (a & (1ul << (63 - j)))
			b |= 1ul << (55 - i);
	}
	return b;
}

/* Input 56 bits, Output 64 bits. */
uint64_t reverse_pc1(uint64_t a)
{
	int i, j;
	uint64_t b;

	b = 0;
	for (i = 0; i < 56; ++i) {
		j = pc1[i] - 1;
		if (a & (1ul << (55 - i)))
			b |= 1ul << (63 - j);
	}
	return b;
}

/* Input 56 bits, Output 48 bits. */
uint64_t apply_pc2(uint64_t a)
{
	int i, j;
	uint64_t b;

	b = 0;
	for (i = 0; i < 48; ++i) {
		j = pc2[i] - 1;
		if (a & (1ul << (55 - j)))
			b |= 1ul << (47 - i);
	}
	return b;
}

/* Input 48 bits, Output 56 bits. */
uint64_t reverse_pc2(uint64_t a)
{
	int i, j;
	uint64_t b;

	b = 0;
	for (i = 0; i < 48; ++i) {
		j = pc2[i] - 1;
		if (a & (1ul << (47 - i)))
			b |= 1ul << (55 - j);
	}
	return b;
}

/* count of pairs. */
/* [sbox][ixor][oxor] */
int ppdt[8][64][16];

/* list of pairs. */
/* [sbox][ixor][oxor][pair] */
int ppdtp [8][64][16][64];

char sbox_lookup(int box, char addr)
{
	int row, col;
	row = addr >> 5;
	row <<= 1;
	row |= addr & 1;

	col = (addr >> 1) & 0xf;
	return sbox[box][row * 16 + col];
}

/* Partial Pairs XOR Distribution Table. */
void dtab()
{
	int i, j, k, ix, ox;
	int box;

	for (box = 0; box < 8; ++box) {
		for (i = 0; i < 64; ++i) {
			for (j = 0; j < 64; ++j) {
				ix = i ^ j;
				ox = sbox_lookup(box, i) ^ sbox_lookup(box, j);
				k = ppdt[box][ix][ox];
				ppdtp[box][ix][ox][k] = i;
				++k;
				ppdt[box][ix][ox] = k;
			}
		}
	}
}

/* ks[0] unused. */
void ksa(uint64_t key, uint64_t ks[17])
{
	int i;
	uint32_t cc[17], dd[17];
	uint8_t shifts[17] = {
		0, /* unused. */
		1,1,2,2,2,2,2,2,
		1,2,2,2,2,2,2,1
	};

	memset(cc, 0, sizeof(cc));
	memset(dd, 0, sizeof(dd));

	/* The most significant byte of the 64bit
	 * number is unused.
	 */
	key = apply_pc1(key);

	dd[0] = key & 0x0fffffff;
	cc[0] = key >> 28;

	for (i = 1; i < 17; ++i) {
		cc[i] = cc[i - 1];
		dd[i] = dd[i - 1];
		cc[i] = (cc[i] << 1) | (cc[i] >> 27);
		dd[i] = (dd[i] << 1) | (dd[i] >> 27);
		if (shifts[i] == 2) {
			cc[i] = (cc[i] << 1) | (cc[i] >> 27);
			dd[i] = (dd[i] << 1) | (dd[i] >> 27);
		}
		cc[i] &= 0x0fffffff;
		dd[i] &= 0x0fffffff;
	}

	for (i = 1; i < 17; ++i) {
		key = cc[i];
		key <<= 28;
		key |= dd[i];
		ks[i] = apply_pc2(key);
	}
}

uint32_t desf(uint32_t r, uint64_t k)
{
	int i;
	uint64_t si;
	uint32_t so;
	char v, addr;

	si = expand(r) ^ k;
	so = 0;
	for (i = 7; i >= 0; --i) {
		addr = si & 0x3f;
		v = sbox_lookup(i, addr);
		so |= (uint32_t)v << (((7 - i) << 2));
		si >>= 6;
	}
	return apply_p(so);
}

/* msg and cph as big endian numbers. */
uint64_t dec(uint64_t cph, uint64_t ks[17], int nr)
{
	int i;
	uint64_t m;
	uint32_t l[17], r[17];

	assert(nr > 0 && nr < 17);

	m = apply_ip(cph);

	l[nr] = m;
	r[nr] = m >> 32;

	for (i = nr; i > 0; --i) {
		r[i - 1] = l[i];
		l[i - 1] = r[i] ^ desf(l[i], ks[i]);
	}

	m = l[0];
	m <<= 32;
	m |= r[0];

	return apply_ipi(m);
}

/* msg and cph as big endian numbers. */
uint64_t enc(uint64_t msg, uint64_t ks[17], int nr)
{
	int i;
	uint64_t c;
	uint32_t l[17], r[17];

	assert(nr > 0 && nr < 17);

	c = apply_ip(msg);

	l[0] = c >> 32;
	r[0] = c;

	for (i = 1; i < nr + 1; ++i) {
		l[i] = r[i - 1];
		r[i] = l[i - 1] ^ desf(r[i - 1], ks[i]);
	}

	c = r[nr];
	c <<= 32;
	c |= l[nr];

	return apply_ipi(c);
}








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

		skc = ppdt[i][ix][ox];
		for (j = 0; j < skc; ++j) {
			sk[j] = ppdtp[i][ix][ox][j] ^ (se[0] & 0x3f);
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

/* The mask has exactly 8 bits set to 1. The addresses of these set bits
 * correspond to the addresses in the key where the bits from v must be
 * copied.
 */
uint64_t apply_mask(uint64_t key, uint64_t mask, int v)
{
	int i, j;
	uint64_t ev;
	key &= ~mask;
	ev = 0;
	for (i = 0, j = 0; i < 64; ++i) {
		/* If the mask bit is 0, ignore. */
		if ((mask & (1ul << (63 - i))) == 0)
			continue;

		if (v & (1 << (7 - j)))
			ev |= 1ul << (63 - i);
		++j;
	}

	return key | ev;
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
		ck = apply_mask(key, mask, i);

		ksa(ck, ks);

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
	int i, j;
	char r;
	struct dc3_ctx c;
	uint64_t ks[17];
	uint64_t mask;
	uint8_t key[8];
	uint8_t p0[8];
	uint8_t p1[8];

	memset(&c, 0, sizeof(c));

	srand(time(NULL));
	dtab();

	assert(getrandom(key, 8, 0) == 8);

	c.key = htobe64(*(const uint64_t *)key);

	/* Zero the don't care bits within the key, for easier comparisons
	 * later.
	 */
	mask = 0;
	for (i = 0; i < 8; ++i) {
		j = xcare_bits[i] - 1;
		mask |= 1ul << (63 - j);
	}
	c.key &= ~mask;

	ksa(c.key, ks);

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
