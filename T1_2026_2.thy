(* Métodos Formais - Trabalho 1
   Integrante: João Pedro da Silva Kriger *)

theory T1_2026_2
  imports Main
begin

primrec cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
cateq1: "cat [] ys = ys" |
cateq2: "cat (x#xs) ys = x#cat xs ys"

primrec reverso :: "'a list \<Rightarrow> 'a list" where
reveq1: "reverso [] = []" |
reveq2: "reverso (x#xs) = cat (reverso xs) [x]"

(* ------------------------------------------------------------------
   Lema 1: associatividade de cat
   Por indução em xs
   P(L) = \<forall>ys zs. cat L (cat ys zs) = cat (cat L ys) zs
   ------------------------------------------------------------------ *)
lemma l1: "\<forall>ys zs :: 'a list . cat xs (cat ys zs) = cat (cat xs ys) zs"
proof (induct xs)
  (* Caso base: P([]) *)
  show "\<forall>ys zs :: 'a list . cat [] (cat ys zs) = cat (cat [] ys) zs"
  proof (rule allI, rule allI)
    (* Seja ys, zs \<in> List(\<tau>) *)
    fix ys zs :: "'a list"
    (* Provar: cat [] (cat ys zs) = cat (cat [] ys) zs *)
    have "cat [] (cat ys zs) = cat ys zs"   by (simp only: cateq1)  (* por cateq1 *)
    also have "... = cat (cat [] ys) zs"    by (simp only: cateq1)  (* por cateq1 *)
    finally show "cat [] (cat ys zs) = cat (cat [] ys) zs" .       (* q.e.d. *)
  qed
next
  (* Caso indutivo: P(x:xs) *)
  (* Seja xs \<in> List(\<tau>), seja x \<in> \<tau> *)
  fix x :: 'a and xs :: "'a list"
  (* HI *)
  assume HI: "\<forall>ys zs :: 'a list . cat xs (cat ys zs) = cat (cat xs ys) zs"
  (* Provar: \<forall>ys zs. cat (x:xs) (cat ys zs) = cat (cat (x:xs) ys) zs *)
  show "\<forall>ys zs :: 'a list . cat (x#xs) (cat ys zs) = cat (cat (x#xs) ys) zs"
  proof (rule allI, rule allI)
    (* Seja ys, zs \<in> List(\<tau>) *)
    fix ys zs :: "'a list"
    have "cat (x#xs) (cat ys zs) = x # cat xs (cat ys zs)" by (simp only: cateq2)  (* por cateq2 *)
    also have "... = x # cat (cat xs ys) zs"               by (simp only: HI)      (* por HI *)
    also have "... = cat (x # cat xs ys) zs"               by (simp only: cateq2)  (* por cateq2 *)
    also have "... = cat (cat (x#xs) ys) zs"               by (simp only: cateq2)  (* por cateq2 *)
    finally show "cat (x#xs) (cat ys zs) = cat (cat (x#xs) ys) zs" .              (* q.e.d. *)
  qed
qed

(* ------------------------------------------------------------------
   Lema 2: [] é elemento neutro à direita de cat
   Por indução em xs
   P(L) = cat L [] = L
   ------------------------------------------------------------------ *)
lemma l2: "cat xs [] = xs"
proof (induct xs)
  (* Caso base: P([]) *)
  (* Provar: cat [] [] = [] *)
  show "cat [] [] = ([] :: 'a list)" by (simp only: cateq1)  (* por cateq1, q.e.d. *)
next
  (* Caso indutivo: P(x:xs) *)
  (* Seja xs \<in> List(\<tau>), seja x \<in> \<tau> *)
  fix x :: 'a and xs :: "'a list"
  (* HI *)
  assume HI: "cat xs [] = xs"
  (* Provar: cat (x:xs) [] = x:xs *)
  have "cat (x#xs) [] = x # cat xs []" by (simp only: cateq2)  (* por cateq2 *)
  also have "... = x # xs"             by (simp only: HI)      (* por HI *)
  finally show "cat (x#xs) [] = x # xs" .                     (* q.e.d. *)
qed

(* ------------------------------------------------------------------
   Lema 3: reverso distribui sobre cat
   Por indução em xs
   P(L) = \<forall>ys. reverso (cat L ys) = cat (reverso ys) (reverso L)
   ------------------------------------------------------------------ *)
lemma l3: "\<forall>ys :: 'a list . reverso (cat xs ys) = cat (reverso ys) (reverso xs)"
proof (induct xs)
  (* Caso base: P([]) *)
  show "\<forall>ys :: 'a list . reverso (cat [] ys) = cat (reverso ys) (reverso [])"
  proof (rule allI)
    (* Seja ys \<in> List(\<tau>) *)
    fix ys :: "'a list"
    (* Provar: reverso (cat [] ys) = cat (reverso ys) (reverso []) *)
    have "reverso (cat [] ys) = reverso ys"      by (simp only: cateq1)  (* por cateq1 *)
    also have "... = cat (reverso ys) []"        by (simp only: l2)      (* por Lema 2 *)
    also have "... = cat (reverso ys) (reverso [])" by (simp only: reveq1)  (* por reveq1 *)
    finally show "reverso (cat [] ys) = cat (reverso ys) (reverso [])" .  (* q.e.d. *)
  qed
next
  (* Caso indutivo: P(x:xs) *)
  (* Seja xs \<in> List(\<tau>), seja x \<in> \<tau> *)
  fix x :: 'a and xs :: "'a list"
  (* HI *)
  assume HI: "\<forall>ys :: 'a list . reverso (cat xs ys) = cat (reverso ys) (reverso xs)"
  (* Provar: \<forall>ys. reverso (cat (x:xs) ys) = cat (reverso ys) (reverso (x:xs)) *)
  show "\<forall>ys :: 'a list . reverso (cat (x#xs) ys) = cat (reverso ys) (reverso (x#xs))"
  proof (rule allI)
    (* Seja ys \<in> List(\<tau>) *)
    fix ys :: "'a list"
    have "reverso (cat (x#xs) ys) = reverso (x # cat xs ys)"   by (simp only: cateq2)  (* por cateq2 *)
    also have "... = cat (reverso (cat xs ys)) [x]"            by (simp only: reveq2)  (* por reveq2 *)
    also have "... = cat (cat (reverso ys) (reverso xs)) [x]"  by (simp only: HI)      (* por HI *)
    also have "... = cat (reverso ys) (cat (reverso xs) [x])"  by (simp only: l1)      (* por Lema 1 *)
    also have "... = cat (reverso ys) (reverso (x#xs))"        by (simp only: reveq2)  (* por reveq2 *)
    finally show "reverso (cat (x#xs) ys) = cat (reverso ys) (reverso (x#xs))" .      (* q.e.d. *)
  qed
qed

(* ------------------------------------------------------------------
   Teorema: reverso é involutiva
   Por indução em xs
   P(L) = reverso (reverso L) = L
   ------------------------------------------------------------------ *)
theorem t1: "reverso (reverso xs) = xs"
proof (induct xs)
  (* Caso base: P([]) *)
  (* Provar: reverso (reverso []) = [] *)
  have "reverso (reverso []) = reverso ([] :: 'a list)" by (simp only: reveq1)  (* por reveq1 *)
  also have "... = []"                                  by (simp only: reveq1)  (* por reveq1 *)
  finally show "reverso (reverso []) = ([] :: 'a list)" .                      (* q.e.d. *)
next
  (* Caso indutivo: P(x:xs) *)
  (* Seja xs \<in> List(\<tau>), seja x \<in> \<tau> *)
  fix x :: 'a and xs :: "'a list"
  (* HI *)
  assume HI: "reverso (reverso xs) = xs"
  (* Provar: reverso (reverso (x:xs)) = x:xs *)
  have "reverso (reverso (x#xs)) = reverso (cat (reverso xs) [x])" by (simp only: reveq2)  (* por reveq2 *)
  also have "... = cat (reverso [x]) (reverso (reverso xs))"       by (simp only: l3)      (* por Lema 3 *)
  also have "... = cat (reverso [x]) xs"                           by (simp only: HI)      (* por HI *)
  (* por def.: [x] e x:[] sao o mesmo termo em Isabelle, logo o passo e imediato *)
  also have "... = cat (cat (reverso []) [x]) xs"                  by (simp only: reveq2)  (* por reveq2 *)
  also have "... = cat (cat [] [x]) xs"                            by (simp only: reveq1)  (* por reveq1 *)
  also have "... = cat [x] xs"                                     by (simp only: cateq1)  (* por cateq1 *)
  (* por def.: [x] e x:[] sao o mesmo termo em Isabelle, logo o passo e imediato *)
  also have "... = x # cat [] xs"                                  by (simp only: cateq2)  (* por cateq2 *)
  also have "... = x # xs"                                         by (simp only: cateq1)  (* por cateq1 *)
  finally show "reverso (reverso (x#xs)) = x # xs" .                                      (* q.e.d. *)
qed

end
