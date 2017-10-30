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

/* DES Implementation header. */

#ifndef _DES_H_
#define _DES_H_

#include <stdint.h>

#define DES_KEY_XCARE_MASK		0x0101010101010101

struct sbox_key {
	int c;
	uint8_t keys[64];
};

uint64_t	apply_ip(uint64_t a);
uint64_t	apply_ipi(uint64_t a);
uint64_t	expand(uint32_t a);
uint32_t	reverse_p(uint32_t a);
uint32_t	apply_p(uint32_t a);
uint64_t	apply_pc1(uint64_t a);
uint64_t	reverse_pc1(uint64_t a);
uint64_t	apply_pc2(uint64_t a);
uint64_t	reverse_pc2(uint64_t a);
char		sbox_lookup(int box, char addr);
void		gen_pairs_xor_tab();
int		pxt_count(int box, int ixor, int oxor);
int		pxt_value(int box, int ixor, int oxor, int i);
void		ksa(uint64_t ks[17], uint64_t key);
void		reverse_ksa(uint64_t *k, uint64_t *m, int nr);
uint32_t	desf(uint32_t r, uint64_t k);
uint64_t	dec(uint64_t cph, const uint64_t ks[17], int nr);
uint64_t	enc(uint64_t msg, const uint64_t ks[17], int nr);
uint64_t	apply_mask(uint64_t key, uint64_t mask, int v, int w);
void		split_subkey(uint8_t keys[8], uint64_t key);
uint64_t	combine_subkey(const uint8_t keys[8]);
uint64_t	next_subkey(int ki[8], const struct sbox_key sk[8]);
bool		contains(const struct sbox_key sk[8], uint64_t key);
#endif
