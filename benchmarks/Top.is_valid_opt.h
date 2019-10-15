extern void body(struct thread_info *);

extern void halt(struct thread_info *);

extern unsigned long long const halt_clo[2];

extern struct thread_info *tinfo;

extern void *call_1(unsigned long long, unsigned long long);

extern void *call_1_export(unsigned long long, unsigned long long);

extern void *call_2(unsigned long long, unsigned long long, unsigned long long);

extern void *call_3_export(unsigned long long, unsigned long long, unsigned long long, unsigned long long);

extern unsigned long long make_eq_eq_refl(void);

extern signed char const names_of_eq[1][8];

extern int const arities_of_eq[1];

extern void elim_eq(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_sum_inl(unsigned long long, unsigned long long **);

extern unsigned long long make_sum_inr(unsigned long long, unsigned long long **);

extern signed char const names_of_sum[2][4];

extern int const arities_of_sum[2];

extern void elim_sum(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_entailment_Entailment(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_entailment[1][11];

extern int const arities_of_entailment[1];

extern void elim_entailment(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_Exists_Exists_cons_tl(unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_Exists_Exists_cons_hd(unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_Exists[2][15];

extern int const arities_of_Exists[2];

extern void elim_Exists(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_PER_Build_PER(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_PER[1][10];

extern int const arities_of_PER[1];

extern void elim_PER(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_comparison_Gt(void);

extern unsigned long long make_comparison_Eq(void);

extern unsigned long long make_comparison_Lt(void);

extern signed char const names_of_comparison[3][3];

extern int const arities_of_comparison[3];

extern void elim_comparison(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_option_None(void);

extern unsigned long long make_option_Some(unsigned long long, unsigned long long **);

extern signed char const names_of_option[2][5];

extern int const arities_of_option[2];

extern void elim_option(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_prod_pair(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_prod[1][5];

extern int const arities_of_prod[1];

extern void elim_prod(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_ex_ex_intro(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_ex[1][9];

extern int const arities_of_ex[1];

extern void elim_ex(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_veristar_result_Aborted(unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_veristar_result_Valid(void);

extern unsigned long long make_veristar_result_C_example(unsigned long long, unsigned long long **);

extern signed char const names_of_veristar_result[3][10];

extern int const arities_of_veristar_result[3];

extern void elim_veristar_result(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_max_type_cmt(unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_max_type[1][4];

extern int const arities_of_max_type[1];

extern void elim_max_type(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_or_or_intror(unsigned long long, unsigned long long **);

extern unsigned long long make_or_or_introl(unsigned long long, unsigned long long **);

extern signed char const names_of_or[2][10];

extern int const arities_of_or[2];

extern void elim_or(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_t__Mkt(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_t_[1][4];

extern int const arities_of_t_[1];

extern void elim_t_(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_expr_Var(unsigned long long, unsigned long long **);

extern unsigned long long make_expr_Nil(void);

extern signed char const names_of_expr[2][4];

extern int const arities_of_expr[2];

extern void elim_expr(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_le_le_S(unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_le_le_n(void);

extern signed char const names_of_le[2][5];

extern int const arities_of_le[2];

extern void elim_le(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_pn_atom_Equ(unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_pn_atom_Nequ(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_pn_atom[2][5];

extern int const arities_of_pn_atom[2];

extern void elim_pn_atom(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_Sorted_Sorted_cons(unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_Sorted_Sorted_nil(void);

extern signed char const names_of_Sorted[2][12];

extern int const arities_of_Sorted[2];

extern void elim_Sorted(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_DefaultRelation_Build_DefaultRelation(void);

extern signed char const names_of_DefaultRelation[1][22];

extern int const arities_of_DefaultRelation[1];

extern void elim_DefaultRelation(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_tree_Leaf(void);

extern unsigned long long make_tree_Node(unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_tree[2][5];

extern int const arities_of_tree[2];

extern void elim_tree(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_enumeration_End(void);

extern unsigned long long make_enumeration_More(unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_enumeration[2][5];

extern int const arities_of_enumeration[2];

extern void elim_enumeration(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_ord_OLT(void);

extern unsigned long long make_ord_OLE(void);

extern unsigned long long make_ord_OEQ(void);

extern signed char const names_of_ord[3][4];

extern int const arities_of_ord[3];

extern void elim_ord(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_space_atom_Next(unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_space_atom_Lseg(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_space_atom[2][5];

extern int const arities_of_space_atom[2];

extern void elim_space_atom(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_sumbool_right(unsigned long long, unsigned long long **);

extern unsigned long long make_sumbool_left(unsigned long long, unsigned long long **);

extern signed char const names_of_sumbool[2][6];

extern int const arities_of_sumbool[2];

extern void elim_sumbool(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_StrictOrder_Build_StrictOrder(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_StrictOrder[1][18];

extern int const arities_of_StrictOrder[1];

extern void elim_StrictOrder(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_True_I(void);

extern signed char const names_of_True[1][2];

extern int const arities_of_True[1];

extern void elim_True(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_pure_atom_Eqv(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_pure_atom[1][4];

extern int const arities_of_pure_atom[1];

extern void elim_pure_atom(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_superposition_result_Valid(void);

extern unsigned long long make_superposition_result_Aborted(unsigned long long, unsigned long long **);

extern unsigned long long make_superposition_result_C_example(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_superposition_result[3][10];

extern int const arities_of_superposition_result[3];

extern void elim_superposition_result(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_assertion_Assertion(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_assertion[1][10];

extern int const arities_of_assertion[1];

extern void elim_assertion(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_InA_InA_cons_tl(unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_InA_InA_cons_hd(unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_InA[2][12];

extern int const arities_of_InA[2];

extern void elim_InA(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_Equivalence_Build_Equivalence(unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_Equivalence[1][18];

extern int const arities_of_Equivalence[1];

extern void elim_Equivalence(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_InT_InLeft(unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_InT_InRight(unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_InT_IsRoot(unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_InT[3][8];

extern int const arities_of_InT[3];

extern void elim_InT(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_INV_Build_INV(unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_INV[1][10];

extern int const arities_of_INV[1];

extern void elim_INV(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_list_cons(unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_list_nil(void);

extern signed char const names_of_list[2][5];

extern int const arities_of_list[2];

extern void elim_list(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_sig_exist(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_sig[1][6];

extern int const arities_of_sig[1];

extern void elim_sig(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_clause_PosSpaceClause(unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_clause_NegSpaceClause(unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_clause_PureClause(unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_clause[3][15];

extern int const arities_of_clause[3];

extern void elim_clause(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_Acc_Acc_intro(unsigned long long, unsigned long long **);

extern signed char const names_of_Acc[1][10];

extern int const arities_of_Acc[1];

extern void elim_Acc(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_CompareSpec_CompLt(unsigned long long, unsigned long long **);

extern unsigned long long make_CompareSpec_CompGt(unsigned long long, unsigned long long **);

extern unsigned long long make_CompareSpec_CompEq(unsigned long long, unsigned long long **);

extern signed char const names_of_CompareSpec[3][7];

extern int const arities_of_CompareSpec[3];

extern void elim_CompareSpec(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_bst_BSLeaf(void);

extern unsigned long long make_bst_BSNode(unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_bst[2][7];

extern int const arities_of_bst[2];

extern void elim_bst(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_positive_xO(unsigned long long, unsigned long long **);

extern unsigned long long make_positive_xH(void);

extern unsigned long long make_positive_xI(unsigned long long, unsigned long long **);

extern signed char const names_of_positive[3][3];

extern int const arities_of_positive[3];

extern void elim_positive(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_nat_S(unsigned long long, unsigned long long **);

extern unsigned long long make_nat_O(void);

extern signed char const names_of_nat[2][2];

extern int const arities_of_nat[2];

extern void elim_nat(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_bool_true(void);

extern unsigned long long make_bool_false(void);

extern signed char const names_of_bool[2][6];

extern int const arities_of_bool[2];

extern void elim_bool(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_HdRel_HdRel_cons(unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_HdRel_HdRel_nil(void);

extern signed char const names_of_HdRel[2][11];

extern int const arities_of_HdRel[2];

extern void elim_HdRel(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_unit_tt(void);

extern signed char const names_of_unit[1][3];

extern int const arities_of_unit[1];

extern void elim_unit(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_color_Red(void);

extern unsigned long long make_color_Black(void);

extern signed char const names_of_color[2][6];

extern int const arities_of_color[2];

extern void elim_color(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_PreOrder_Build_PreOrder(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_PreOrder[1][15];

extern int const arities_of_PreOrder[1];

extern void elim_PreOrder(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_rrspec_rrleft(unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_rrspec_rrelse(unsigned long long, unsigned long long, unsigned long long **);

extern unsigned long long make_rrspec_rrright(unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_rrspec[3][8];

extern int const arities_of_rrspec[3];

extern void elim_rrspec(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_Z_Zneg(unsigned long long, unsigned long long **);

extern unsigned long long make_Z_Z0(void);

extern unsigned long long make_Z_Zpos(unsigned long long, unsigned long long **);

extern signed char const names_of_Z[3][5];

extern int const arities_of_Z[3];

extern void elim_Z(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_ce_type_CexpR(void);

extern unsigned long long make_ce_type_CexpL(void);

extern unsigned long long make_ce_type_CexpEf(void);

extern signed char const names_of_ce_type[3][7];

extern int const arities_of_ce_type[3];

extern void elim_ce_type(unsigned long long, unsigned long long *, unsigned long long **);

extern unsigned long long make_and_conj(unsigned long long, unsigned long long, unsigned long long **);

extern signed char const names_of_and[1][5];

extern int const arities_of_and[1];

extern void elim_and(unsigned long long, unsigned long long *, unsigned long long **);


