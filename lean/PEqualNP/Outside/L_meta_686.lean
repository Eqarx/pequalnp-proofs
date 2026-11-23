import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_686 : ∀ (m n r : ℕ) (S : Fin m → Finset (Fin n)),
    (∀ x y : Fin n, x ≠ y → ∃ i : Fin m, x ∈ S i ∧ y ∈ S i) →
    (∀ x : Fin n, (Finset.univ.filter (fun i : Fin m => x ∈ S i)).card = r) →
    ∀ B : Finset (Fin n),
      (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)).card + B.card ≤ B.card * r + 1 := by
  intro m n r S pair regular B
  classical
  let incident (x : Fin n) : Finset (Fin m) :=
    Finset.univ.filter (fun i => x ∈ S i)
  let hit (T : Finset (Fin n)) : Finset (Fin m) :=
    Finset.univ.filter (fun i => ∃ x ∈ T, x ∈ S i)
  have card_incident (x : Fin n) : (incident x).card = r := regular x
  have hit_insert (a : Fin n) (T : Finset (Fin n)) :
      hit (insert a T) = incident a ∪ hit T := by
    ext i
    simp only [hit, incident, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨x, hx, hxi⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inl hxi
      · exact Or.inr ⟨x, hx, hxi⟩
    · rintro (hia | ⟨x, hx, hxi⟩)
      · exact ⟨a, Finset.mem_insert_self _ _, hia⟩
      · exact ⟨x, Finset.mem_insert_of_mem hx, hxi⟩
  have hit_empty : hit ∅ = ∅ := by
    ext i
    simp [hit]
  change (hit B).card + B.card ≤ B.card * r + 1
  induction B using Finset.induction_on with
  | empty => simp [hit_empty]
  | @insert a T ha ih =>
      rw [hit_insert, Finset.card_insert_of_notMem ha, Nat.add_mul, Nat.one_mul]
      by_cases hT : T = ∅
      · subst T
        simp [hit_empty, card_incident]
      · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hT
        have hab : a ≠ b := fun e => ha (e ▸ hb)
        obtain ⟨i, hia, hib⟩ := pair a b hab
        have hii : i ∈ incident a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hia⟩
        have hit_i : i ∈ hit T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hb, hib⟩
        have hpos : 0 < (incident a ∩ hit T).card :=
          Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr ⟨hii, hit_i⟩⟩
        have hcard := Finset.card_union_add_card_inter (incident a) (hit T)
        rw [card_incident] at hcard
        omega
