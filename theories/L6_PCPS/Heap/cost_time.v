
  





  (** The cost of constructing environments when evaluating e *)
  Fixpoint cost_space_exp (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => 1 + length ys + cost_space_exp e
      | Ecase x l =>
        (fix sizeOf_l l :=
               match l with
                 | [] => 0
                 | (t, e) :: l => max (cost_space_exp e) (sizeOf_l l)
               end) l
      | Eproj x _ _ y e => cost_space_exp e
      | Efun B e => max
                     (1 + PS.cardinal (fundefs_fv B) + (* env *)
                      3 * (numOf_fundefs B) + (* closures *)
                      cost_space_exp e)
                     (1 + PS.cardinal (fundefs_fv B) + cost_space_funs B)
      | Eapp x _ ys => 0
      | Eprim x _ ys e => cost_space_exp e
      | Ehalt x => 0
    end
  with cost_space_funs (f : fundefs) : nat :=
         match f with
         | Fcons _ _ _ e B =>
           max (cost_space_exp e) (cost_space_funs B) 
         | Fnil => 0
         end.

  
  Definition cost_space_heap H1 := cost_heap (fun B => cost_space_funs B + (1 + PS.cardinal (fundefs_fv B))) H1.

      
  (** Heap delta *)
  Definition size_cc_block (b : block) : nat :=
    match b with
      | Constr _ vs => 0
      | Clos v1 rho => 2
      | Env rho => PS.cardinal (@mset (key_set rho) _)
    end.

  Definition size_cc_loc (l : loc) H1 :=
  match get l H1 with
    | Some b => size_val b
    | None => 0
  end.

  (** The heap overheap of closure conversion -- remove functions not yet projected *)

  Definition size_cc_heap (H : heap block) :=
    size_with_measure size_cc_block H.
  
  
  

    (** Sizes of equivalent blocks *)

  Lemma block_equiv_size_cc_block b bl1 bl2 H1 H2 :
    block_equiv (b, H1, bl1) (id, H2, bl2) ->
    size_cc_block bl1 = size_cc_block bl2.
  Proof. 
    intros Hbl. eapply block_equiv_subst_block in Hbl.
    destruct bl1; destruct bl2; try contradiction.
    - reflexivity.
    - reflexivity.
    - simpl in *.
      rewrite !PS.cardinal_spec. erewrite elements_eq. reflexivity.
      eapply Same_set_From_set.
      rewrite <- !mset_eq. eassumption.
  Qed.

