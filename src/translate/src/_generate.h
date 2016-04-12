/* 24.12.2008 last modification: 26.06.2013
Copyright (c) 2008-2013 by Siegfried Koepf

This file is distributed under the terms of the GNU General Public License
version 3 as published by the Free Software Foundation.
For information on usage and redistribution and for a disclaimer of all
warranties, see the file COPYING in this distribution.

combinatorial generation functions public interfaces
*/

#ifndef _GENERATE_H
#define _GENERATE_H

//return values of generation functions
#define GEN_NEXT  0 //ok, print and continue
#define GEN_TERM  1 //ok, terminate
#define GEN_EMPTY 2 //ok, print EMPTY SET and continue
#define GEN_ERROR 3 //an error occured, print an error message and terminate

//combinatorial generation functions
int gen_comb_norep_lex_init(unsigned char *vector, const unsigned char n, const unsigned char k);
int gen_comb_norep_lex_next(unsigned char *vector, const unsigned char n, const unsigned char k);

int gen_comb_norep_revcolex_init(unsigned char *vector, const unsigned char n, const unsigned char k);
int gen_comb_norep_revcolex_next(unsigned char *vector, const unsigned char k);

int gen_comb_rep_lex_init(unsigned char *vector, const unsigned char n, const unsigned char k);
int gen_comb_rep_lex_next(unsigned char *vector, const unsigned char n, const unsigned char k);

int gen_comb_rep_revcolex_init(unsigned char *vector, const unsigned char n, const unsigned char k);
int gen_comb_rep_revcolex_next(unsigned char *vector, const unsigned char k);

int gen_part_revlex_init(unsigned char *vector, const unsigned char n, unsigned char *k);
int gen_part_revlex_next(unsigned char *vector, unsigned char *k);

int gen_k_part_colex_init(unsigned char *vector, const unsigned char n, const unsigned char k);
int gen_k_part_colex_next(unsigned char *vector, const unsigned char k);

int gen_k_comp_colex_init(unsigned char *vector, const unsigned char n, const unsigned char k);
int gen_k_comp_colex_next(unsigned char *vector, const unsigned char k);

int gen_vari_rep_lex_init(unsigned char *vector, const unsigned char m, const unsigned char n);
int gen_vari_rep_lex_next(unsigned char *vector, const unsigned char m, const unsigned char n);

int gen_vari_rep_colex_init(unsigned char *vector, const unsigned char m, const unsigned char n);
int gen_vari_rep_colex_next(unsigned char *vector, const unsigned char m, const unsigned char n);

int gen_neck_lex_init(unsigned char *vector, const unsigned char m, const unsigned char n);
int gen_neck_lex_next(unsigned char *vector, const unsigned char m, const unsigned char n);

int gen_perm_rep_lex_init(const unsigned char n);
int gen_perm_rep_lex_next(unsigned char *vector, const unsigned char n);

#endif
