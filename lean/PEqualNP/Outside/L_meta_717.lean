import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_717

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def value (xs : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => xs.getD i false))

private def step (xs : List Bool) (g : Gate) : List Bool := xs ++ [value xs g]

private lemma foldLength (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step, Nat.add_left_comm, Nat.add_comm]

private lemma foldGet (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (gs.foldl step xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
      rw [List.foldl_cons, ih (step xs g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi

private lemma readSetNe (xs : List Bool) (k i : ℕ) (b : Bool) (hi : i ≠ k) :
    (xs.set k b).getD i false = xs.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne hi.symm]

private lemma foldSet (gs : List Gate) (xs : List Bool) (k : ℕ) (b : Bool)
    (hk : k < xs.length) (h : ∀ g ∈ gs, k ∉ g.inputs) :
    gs.foldl step (xs.set k b) = (gs.foldl step xs).set k b := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
      have hn := h g (List.mem_cons_self)
      have hv : value (xs.set k b) g = value xs g := by
        unfold value
        congr 1
        apply List.map_congr_left
        intro i hi
        exact readSetNe xs k i b (fun e => hn (e ▸ hi))
      have he : step (xs.set k b) g = (step xs g).set k b := by
        unfold step
        rw [hv, List.set_append_left _ _ hk]
      simp only [List.foldl_cons, he]
      exact ih (step xs g) (by simp [step]; omega) (fun a ha => h a (List.mem_cons_of_mem _ ha))

private lemma valueMono (xs ys : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hmono : ∀ i ∈ g.inputs, xs.getD i false = true → ys.getD i false = true) :
    value xs g = true → value ys g = true := by
  unfold value
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hh a ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact hmono i hi (hh _ ⟨i, hi, rfl⟩)
  · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨a, ⟨i, hi, rfl⟩, ha⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hmono i hi ha⟩

private lemma listSnoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

private lemma splitGates (n j : ℕ) (C : Circuit) (g : Gate)
    (hg : C.gates[j]? = some g)
    (hone : ∀ (j' : ℕ) (g' : Gate), C.gates[j']? = some g' → n ∈ g'.inputs → j' = j) :
    ∃ pre post : List Gate, C.gates = pre ++ g :: post ∧ pre.length = j ∧
      (∀ a ∈ pre, n ∉ a.inputs) ∧ ∀ a ∈ post, n ∉ a.inputs := by
  obtain ⟨hj, he⟩ := List.getElem?_eq_some_iff.mp hg
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hs : C.gates = pre ++ g :: post := by
    unfold pre post
    rw [← he, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hp : pre.length = j := by simp [pre, Nat.min_eq_left hj.le]
  refine ⟨pre, post, hs, hp, ?_, ?_⟩
  · intro a ha han
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    have hlt := (List.getElem?_eq_some_iff.mp hi).1
    have hC : C.gates[i]? = some a := by rw [hs, List.getElem?_append_left hlt]; exact hi
    have heq := hone i a hC han
    omega
  · intro a ha han
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    have hC : C.gates[j+1+i]? = some a := by
      rw [hs, List.getElem?_append_right (by omega), show j+1+i-pre.length=i+1 by omega]
      exact hi
    have heq := hone (j+1+i) a hC han
    omega

private def redirect (n k i : ℕ) : ℕ :=
  if i < k then i else if i = k then n else i - 1

private def redirectGate (n k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (redirect n k)⟩

private lemma insertAppend (k : ℕ) (z : Bool) (xs ys : List Bool) (hk : k ≤ xs.length) :
    (xs ++ ys).insertIdx k z = xs.insertIdx k z ++ ys := by
  induction xs generalizing k with
  | nil =>
      have : k = 0 := by simpa using hk
      subst k
      rfl
  | cons x xs ih =>
      cases k with
      | zero => rfl
      | succ k =>
          simp only [List.cons_append, List.insertIdx_succ_cons]
          rw [ih k (by simpa using hk)]

private lemma redirectRead (n k i : ℕ) (z : Bool) (xs : List Bool)
    (hk : k ≤ xs.length) (hn : xs.getD n false = z) :
    (xs.insertIdx k z).getD i false = xs.getD (redirect n k i) false := by
  unfold redirect
  split
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_insertIdx_of_lt (by omega : i < k)]
  · split
    · subst i
      rw [hn, List.getD_eq_getElem?_getD, List.getElem?_insertIdx_self]
      simp [hk]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_insertIdx_of_gt (by omega : k < i)]

private lemma foldRedirect (n k : ℕ) (z : Bool) (gs : List Gate) (xs : List Bool)
    (hk : k ≤ xs.length) (hn : n < k) (hnx : xs.getD n false = z) :
    gs.foldl step (xs.insertIdx k z) =
      ((gs.map (redirectGate n k)).foldl step xs).insertIdx k z := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
      have hstep : step (xs.insertIdx k z) g = (step xs (redirectGate n k g)).insertIdx k z := by
        simp only [step, value, redirectGate, List.map_map, Function.comp_def, redirectRead n k _ z xs hk hnx,
          insertAppend k z xs _ hk]
      simp only [List.map_cons, List.foldl_cons, hstep]
      apply ih
      · simp [step]; omega
      · unfold step
        rw [List.getD_append _ _ _ _ (by omega), hnx]

private lemma gateAlias (n : ℕ) (g : (Fin n → Bool) → Bool) (C : Circuit)
    (gate : Gate) (pre post : List Gate)
    (hs : C.gates = pre ++ gate :: post)
    (hpre : ∀ a ∈ pre, n ∉ a.inputs) (hpost : ∀ a ∈ post, n ∉ a.inputs)
    (hop : gate.op = GateOp.and ∨ gate.op = GateOp.or)
    (hno : C.output ≠ n)
    (hev : ∀ x : Fin (n + 1) → Bool,
      C.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i => x i.castSucc))) :
    ∀ (y : Fin n → Bool) (b : Bool),
      value (pre.foldl step (List.ofFn y ++ [b])) gate = b := by
  intro y
  let xs (b : Bool) := List.ofFn y ++ [b]
  let preW (b : Bool) := pre.foldl step (xs b)
  have he (b : Bool) : C.eval (xs b) = xor b (g y) := by
    simpa only [xs, listSnoc, Fin.snoc_last, Fin.snoc_castSucc] using hev (Fin.snoc y b)
  have len : n < (preW false).length := by simp [preW, xs, foldLength]; omega
  have hp : preW true = (preW false).set n true := by
    have hx : xs true = (xs false).set n true := by
      unfold xs
      rw [List.set_append_right _ _ (by simp), List.length_ofFn, Nat.sub_self]
      rfl
    unfold preW
    rw [hx, foldSet _ _ _ _ (by simp [xs]) hpre]
  have hmono : value (preW false) gate = true → value (preW true) gate = true := by
    apply valueMono _ _ _ hop
    intro i _ hi
    by_cases hn : i = n
    · subst i
      have hf : (preW false).getD n false = false := by
        unfold preW xs
        rw [foldGet _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp),
          List.length_ofFn, Nat.sub_self]
        rfl
      rw [hf] at hi
      cases hi
    · rwa [hp, readSetNe _ _ _ _ hn]
  have hdiff : value (preW false) gate ≠ value (preW true) gate := by
    intro eq
    have ht : step (preW true) gate = (step (preW false) gate).set n true := by
      unfold step
      rw [← eq, hp, List.set_append_left _ _ len]
    have hpost' :
      post.foldl step (step (preW true) gate) =
        (post.foldl step (step (preW false) gate)).set n true := by
      rw [ht, foldSet _ _ _ _ (by simp [step]; omega) hpost]
    have hval : C.eval (xs true) = C.eval (xs false) := by
      unfold Circuit.eval Circuit.wires
      change (C.gates.foldl step (xs true)).getD C.output false = (C.gates.foldl step (xs false)).getD C.output false
      simp only [hs, List.foldl_append, List.foldl_cons]
      change (post.foldl step (step (preW true) gate)).getD C.output false =
        (post.foldl step (step (preW false) gate)).getD C.output false
      rw [hpost', readSetNe _ _ _ _ hno]
    rw [he, he] at hval
    cases e : g y <;> simp [e] at hval
  intro b
  change value (preW b) gate = b
  cases e0 : value (preW false) gate <;> cases e1 : value (preW true) gate <;>
    simp [e0, e1] at hmono hdiff ⊢
  cases b <;> assumption

end PEqualNP.Outside.L_meta_717

theorem PEqualNP.Outside.L_meta_717 : ∀ (n : ℕ) (g : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ y y' : Fin n → Bool, g y ≠ g y') → PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin (n + 1) → Bool, C.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) → (∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C' → (∀ x : Fin (n + 1) → Bool, C'.eval (List.ofFn x) = xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) → C.size ≤ C'.size) → ¬ ∃ (j : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some h ∧ (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n ∈ h.inputs ∧ ∀ (j' : ℕ) (h' : PEqualNP.CircuitLowerBounds.Gate), C.gates[j']? = some h' → n ∈ h'.inputs → j' = j := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_717 in
  intro n g C hnon hC hev hmin hbad
  obtain ⟨j, gate, hgate, hop, _, hone⟩ := hbad
  obtain ⟨pre, post, hs, hj, hpre, hpost⟩ := splitGates n j C gate hgate hone
  have hno : C.output ≠ n := by
    intro hOut
    have hzero (y : Fin n → Bool) : g y = false := by
      have he := hev (Fin.snoc y false)
      simp only [listSnoc, Fin.snoc_last, Fin.snoc_castSucc] at he
      have he' : C.eval (List.ofFn y ++ [false]) = g y := by simpa using he
      rw [← he']
      unfold Circuit.eval Circuit.wires
      change (C.gates.foldl step (List.ofFn y ++ [false])).getD C.output false = false
      rw [hOut, foldGet _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp),
        List.length_ofFn, Nat.sub_self]
      rfl
    obtain ⟨a,b,hne⟩ := hnon
    exact hne ((hzero a).trans (hzero b).symm)
  have halias := gateAlias n g C gate pre post hs hpre hpost hop hno hev
  let k := n+1+j
  let C' : Circuit := ⟨pre ++ post.map (redirectGate n k), redirect n k C.output⟩
  have hC' : FanInTwo C' := by
    intro h hh
    change h ∈ pre ++ post.map (redirectGate n k) at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hC h (by rw [hs]; exact List.mem_append_left _ hh)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hh
      have ha' := hC a (by rw [hs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha))
      exact ⟨ha'.1, by simpa [redirectGate] using ha'.2⟩
  have heC (x : Fin (n + 1) → Bool) : C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    let y : Fin n → Bool := fun i => x i.castSucc
    let z := x (Fin.last n)
    have hx : List.ofFn x = List.ofFn y ++ [z] := by rw [List.ofFn_succ']; simp [y,z]
    let w := pre.foldl step (List.ofFn x)
    have hw : w.length = k := by
      rw [foldLength, List.length_ofFn, hj]
    have hz : w.getD n false = z := by
      unfold w
      rw [foldGet _ _ _ (by simp), hx, List.getD_append_right _ _ _ _ (by simp),
        List.length_ofFn, Nat.sub_self]
      rfl
    have hgateVal : value w gate = z := by unfold w; rw [hx]; exact halias y z
    have hstep : step w gate = w.insertIdx k z := by
      unfold step
      rw [hgateVal, ← hw, List.insertIdx_length_self]
    change ((pre ++ post.map (redirectGate n k)).foldl step (List.ofFn x)).getD (redirect n k C.output) false =
      (C.gates.foldl step (List.ofFn x)).getD C.output false
    rw [hs, List.foldl_append, List.foldl_append, List.foldl_cons]
    change ((post.map (redirectGate n k)).foldl step w).getD (redirect n k C.output) false =
      (post.foldl step (step w gate)).getD C.output false
    rw [hstep, foldRedirect n k z post w hw.ge (by unfold k; omega) hz]
    symm
    apply redirectRead
    · have hh := foldLength (post.map (redirectGate n k)) w
      omega
    · exact (foldGet _ _ _ (by unfold k at hw; omega)).trans hz
  have hc := hmin C' hC' (fun x => (heC x).trans (hev x))
  simp [C', Circuit.size, hs] at hc
