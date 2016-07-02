lemma "reverse (reverse xs) == xs"
  apply (induct xs)
  apply (simp_all add: reverse_conc)
  done
