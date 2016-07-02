theory Seq
imports Main
begin

(** begin #def-seq-conc *)
datatype '\<alpha> seq = Empty | Seq '\<alpha> "'\<alpha> seq" 

fun conc :: "'\<alpha> seq \<Rightarrow> '\<alpha> seq \<Rightarrow> '\<alpha> seq"
where
  "conc Empty ys = ys"
| "conc (Seq x xs) ys = Seq x (conc xs ys)"
(** end #def-seq-conc *)

(** begin #fun-reverse *)
fun reverse :: "'\<alpha> seq \<Rightarrow> '\<alpha> seq"
where
  "reverse Empty = Empty"
| "reverse (Seq x xs) = conc (reverse xs) (Seq x Empty)"
(** end #fun-reverse *)

lemma conc_empty: "conc xs Empty = xs"
  by (induct xs, simp_all)

lemma conc_assoc: "conc (conc xs ys) zs = conc xs (conc ys zs)"
  by (induct xs, simp_all)

(** begin #reverse-conc *)
lemma reverse_conc: "reverse (conc xs ys) = conc (reverse ys) (reverse xs)"
  apply (induct xs)
  apply (simp_all add: conc_empty conc_assoc) 
  done
(** end #reverse-conc *)

(** begin #reverse-reverse *)
lemma reverse_reverse: "reverse (reverse xs) = xs"
  oops
(** end #reverse-reverse *)


end
