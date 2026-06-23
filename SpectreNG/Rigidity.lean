import SpectreNG.Topology
import SpectreNG.Sieve
import Mathlib.Data.List.Nodup
import Lean

open LatticePoint


lemma list_filter_len_le (f : α → Bool) (l : List α) : (l.filter f).length ≤ l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons]
    split
    · dsimp; omega
    · dsimp; omega

lemma patchSize_drop_tile {t : PlacedTile} {tiles : Patch} (h_mem : t ∈ tiles) :
  patchSize (tiles.filter (fun x => decide (x ≠ t))) < patchSize tiles := by
  dsimp [patchSize]
  induction tiles generalizing t with
  | nil => cases h_mem
  | cons head tail ih =>
    rw [List.filter_cons]
    by_cases h_eq : head = t
    · have h_cond : decide (head ≠ t) = false := by
        rw [h_eq]
        simp
      rw [h_cond]
      dsimp
      have h_le := list_filter_len_le (fun x => decide (¬ x = t)) tail
      omega
    · have h_mem' : t ∈ tail := by
        cases h_mem with
        | head => contradiction
        | tail _ ht => exact ht
      have ih' := ih h_mem'
      split
      · dsimp; omega
      · dsimp; omega


/-- The Downward Peeling Induction Principle:
    A custom induction schema based on the patch size metric, proved using well-founded recursion. -/
theorem downward_peeling_induction {M : Patch → Prop}
  (h_empty : M [])
  (h_peel : ∀ (tiles : Patch), tiles ≠ [] → 
    (∀ (sub : Patch), patchSize sub < patchSize tiles → M sub) → M tiles)
  (tiles : Patch) : M tiles := by
  by_cases h : tiles = []
  · subst h; exact h_empty
  · apply h_peel tiles h
    intro sub h_sub
    exact downward_peeling_induction h_empty h_peel sub
termination_by patchSize tiles

/-- The true structural rigidity property claim: if a patch is valid, 
    any other valid patch completing the same simply connected boundary path is equal to it (up to permutation). -/
def RigidityProperty (tiles : Patch) : Prop :=
  ValidPatch tiles → ∀ (other : Patch) (p : Path), 
    ValidPatch other → eulerCharacteristic tiles = 1 → 
    CompletesPath tiles p → CompletesPath other p → List.Perm tiles other

theorem rigidity_base : RigidityProperty [] := by
  intro _h_valid other p _h_other_val _h_euler h_comp h_comp_other
  have h_empty : p = [] := completesPath_nil_empty p h_comp
  have h_other_empty : other = [] := by
    by_cases h_ne : other = []
    · exact h_ne
    · have hp_ne : p ≠ [] := non_empty_patch_perimeter h_ne h_comp_other
      contradiction
  rw [h_other_empty]


-- exists_anchor_tile relocated to Topology.lean to avoid circular dependency

lemma filter_not_mem {α : Type} [DecidableEq α] (x : α) (l : List α) (h : x ∉ l) :
  l.filter (fun y => decide (y ≠ x)) = l := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    have h_not : head ≠ x := by
      intro hc
      subst hc
      apply h
      apply List.Mem.head
    have h_not_in : x ∉ tail := by
      intro hc
      apply h
      apply List.Mem.tail _ hc
    dsimp [List.filter]
    have h_cond : decide (head ≠ x) = true := by
      simp [h_not]
    rw [h_cond]
    dsimp
    congr 1
    exact ih h_not_in

lemma nodup_erase_eq_filter {α : Type} [DecidableEq α] (x : α) (l : List α) (nd : l.Nodup) :
  l.erase x = l.filter (fun y => decide (y ≠ x)) := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    have nd_tail : tail.Nodup := by
      cases nd
      assumption
    dsimp [List.erase, List.filter]
    by_cases h_eq : head = x
    · subst head
      have h_beq : (x == x) = true := beq_self_eq_true x
      rw [h_beq]
      have h_cond : decide (x ≠ x) = false := by simp
      rw [h_cond]
      have hx : x ∉ tail := by
        cases nd
        rename_i nd_tail h_not_in
        intro hc
        exact h_not_in x hc rfl
      exact (filter_not_mem x tail hx).symm
    · have h_beq : (head == x) = false := by
        simp [h_eq]
      rw [h_beq]
      have h_cond : decide (head ≠ x) = true := by
        simp [h_eq]
      rw [h_cond]
      dsimp
      congr 1
      exact ih nd_tail

lemma perm_of_filter_perm_and_mem {α : Type} [DecidableEq α] (x : α) (l1 l2 : List α)
  (h1 : x ∈ l1) (h2 : x ∈ l2) (d1 : l1.Nodup) (d2 : l2.Nodup)
  (hp : (l1.filter (fun y => decide (y ≠ x))).Perm (l2.filter (fun y => decide (y ≠ x)))) :
  l1.Perm l2 := by
  have he1 := nodup_erase_eq_filter x l1 d1
  have he2 := nodup_erase_eq_filter x l2 d2
  have hp_erase : (l1.erase x).Perm (l2.erase x) := by
    rw [he1, he2]
    exact hp
  have h_perm1 := List.perm_cons_erase h1
  have h_perm2 := List.perm_cons_erase h2
  have h_perm_both : (x :: l1.erase x).Perm (x :: l2.erase x) := List.Perm.cons x hp_erase
  exact List.Perm.trans h_perm1 (List.Perm.trans h_perm_both h_perm2.symm)
lemma validPatch_nodup (tiles : Patch) (h : ValidPatch tiles) :
  tiles.Nodup := by
  exact h.1

lemma validPatch_tail_of_cons {head : PlacedTile} {tail : Patch} (h : ValidPatch (head :: tail)) :
  ValidPatch tail := by
  exact (Iff.mp (validPatch_cons head tail) h).1

lemma validPatch_singleton_of_cons {head : PlacedTile} {tail : Patch} (_ : ValidPatch (head :: tail)) :
  ValidPatch [head] := by
  exact validPatch_singleton head

lemma validPatch_cons_of_sub {head : PlacedTile} {tail c : Patch} (h_val : ValidPatch (head :: tail))
  (h_sub : c ⊆ tail) (h_c : ValidPatch c) : ValidPatch (head :: c) := by
  rw [validPatch_cons]
  refine ⟨h_c, ?_, ?_⟩
  · intro h_in
    have h_in_tail := h_sub h_in
    have h_not_in_tail := (Iff.mp (validPatch_cons head tail) h_val).2.1
    exact h_not_in_tail h_in_tail
  · intro t2 ht2
    have ht2_tail := h_sub ht2
    have h_overlap := (Iff.mp (validPatch_cons head tail) h_val).2.2 t2 ht2_tail
    exact h_overlap

lemma partitionPatchComponents_subset {t : PlacedTile} {tiles : Patch} {c : Patch}
  (h_mem : c ∈ partitionPatchComponents t tiles) : c ⊆ tiles := by
  induction tiles generalizing c with
  | nil =>
    dsimp [partitionPatchComponents] at h_mem
    cases h_mem
  | cons head tail ih =>
    simp [partitionPatchComponents] at h_mem
    by_cases h_eq : head = t
    · simp [h_eq] at h_mem
      have h_sub := ih h_mem
      intro x hx
      exact List.mem_cons_of_mem head (h_sub hx)
    · simp [h_eq] at h_mem
      rcases h_part : partitionPatchComponents t tail with _ | ⟨c', cs'⟩
      · rw [h_part] at h_mem
        simp at h_mem
        subst h_mem
        intro x hx
        simp at hx
        subst hx
        exact List.mem_cons_self
      · rw [h_part] at h_mem
        simp at h_mem
        cases h_mem with
        | inl h_c_eq =>
          subst h_c_eq
          have h_c'_mem : c' ∈ partitionPatchComponents t tail := by rw [h_part]; exact List.Mem.head _
          have h_sub_tail := ih h_c'_mem
          intro x hx
          cases hx with
          | head => exact List.mem_cons_self
          | tail _ hx_in => exact List.mem_cons_of_mem head (h_sub_tail hx_in)
        | inr h_cs_mem =>
          have h_c_mem_tail : c ∈ partitionPatchComponents t tail := by rw [h_part]; exact List.Mem.tail _ h_cs_mem
          have h_sub_tail := ih h_c_mem_tail
          intro x hx
          exact List.mem_cons_of_mem head (h_sub_tail hx)

lemma validPatch_of_mem_partition {t : PlacedTile} {tiles : Patch} {sub : Patch}
  (h_val : ValidPatch tiles) (h_mem : sub ∈ partitionPatchComponents t tiles) :
  ValidPatch sub := by
  induction tiles generalizing sub with
  | nil =>
    -- Base Case: partitionPatchComponents evaluates to [], making h_mem impossible
    dsimp [partitionPatchComponents] at h_mem
    cases h_mem
  | cons head tail ih =>
    -- Inductive Step: Simplify the recursive definition and branch on head = t
    by_cases h_eq : head = t
    · subst h_eq
      simp [partitionPatchComponents] at h_mem
      have h_val_tail := validPatch_tail_of_cons h_val
      exact ih h_val_tail h_mem
    · simp [partitionPatchComponents, h_eq] at h_mem
      have h_val_tail := validPatch_tail_of_cons h_val
      rcases h_part : partitionPatchComponents t tail with _ | ⟨c, cs⟩
      · rw [h_part] at h_mem
        simp at h_mem
        subst h_mem
        exact validPatch_singleton_of_cons h_val
      · rw [h_part] at h_mem
        simp at h_mem
        cases h_mem with
        | inl h_sub_eq =>
          subst h_sub_eq
          have h_c_mem : c ∈ partitionPatchComponents t tail := by rw [h_part]; exact List.Mem.head _
          have h_val_c := ih h_val_tail h_c_mem
          have h_sub := partitionPatchComponents_subset h_c_mem
          exact validPatch_cons_of_sub h_val h_sub h_val_c
        | inr h_cs_mem =>
          have h_sub_in : sub ∈ partitionPatchComponents t tail := by rw [h_part]; exact List.Mem.tail _ h_cs_mem
          exact ih h_val_tail h_sub_in

lemma perm_of_erased_perm {α : Type} [DecidableEq α] (x : α) (l1 l2 : List α)  
  (h1 : x ∈ l1) (h2 : x ∈ l2) (d1 : l1.Nodup) (d2 : l2.Nodup)  
  (hp : List.Perm (l1.filter (fun t => decide (t ≠ x))) (l2.filter (fun t => decide (t ≠ x)))) :  
  List.Perm l1 l2 := perm_of_filter_perm_and_mem x l1 l2 h1 h2 d1 d2 hp


lemma perm_of_partition_components_perm {t : PlacedTile} {l1 l2 : List PlacedTile}  
  (h_val1 : ValidPatch l1) (h_val2 : ValidPatch l2)
  (h1 : t ∈ l1) (h2 : t ∈ l2) (d1 : l1.Nodup) (d2 : l2.Nodup)  
  (hp : ∀ sub_patch ∈ partitionPatchComponents t l1, ∃ sub_other ∈ partitionPatchComponents t l2, List.Perm sub_patch sub_other) :  
  List.Perm l1 l2 := by  
  have h_recombine := component_permutation_recombine t l1 l2 [] h_val1 h_val2 hp
  exact perm_of_filter_perm_and_mem t l1 l2 h1 h2 d1 d2 h_recombine

/-- The Global Rigidity Theorem: proven using downward peeling induction. -/
theorem global_rigidity_theorem (tiles : Patch) : RigidityProperty tiles := by
  apply downward_peeling_induction (M := RigidityProperty)
  · -- Case 1: Base Case (empty patch)
    exact rigidity_base
  · -- Inductive Step: Peeling
    intro t_patch h_nonempty ih h_val other p h_other_val h_euler h_comp h_comp_other
    -- Find a lookahead window w of length 5:
    have h_window := find_lookahead_window h_nonempty h_euler h_comp
    rcases h_window with ⟨w, h_sub, h_w_len, h_w_valid⟩
    have h_w_comp : CompletesPath t_patch w := subpath_completion h_comp h_sub
    have h_w_unique : UniquelyDetermined w := aperiodic_holography_lock w h_w_len h_w_valid
    -- We obtain the unique locked/anchor tile from the patch:
    have h_locked : ∃ t ∈ t_patch, DirectedEdge.mk ⟨0, 0, 0, 0⟩ (⟨0, 0, 0, 0⟩ + dirToVec 0) 0 ∈ generateTileEdges t := exists_anchor_tile_existence w h_w_comp h_w_len h_w_valid
    rcases h_locked with ⟨locked_tile, h_in, h_ori⟩
    have h_w_comp_other : CompletesPath other w := subpath_completion h_comp_other h_sub
    have h_anchor : IsAnchor locked_tile w t_patch := ⟨h_in, h_ori⟩
    have h_in_other : locked_tile ∈ other := anchor_forced_in_other h_w_len h_w_valid h_val h_other_val h_w_unique h_w_comp h_w_comp_other h_anchor
    have d1 : t_patch.Nodup := validPatch_nodup t_patch h_val
    have d2 : other.Nodup := validPatch_nodup other h_other_val
    by_cases h_contig : AreEdgesContiguousInPath locked_tile p
    · -- Case 2: Contiguous (Single-Patch Contraction / Erosion)
      have h_lt : patchSize (t_patch.filter (fun t => decide (t ≠ locked_tile))) < patchSize t_patch :=
        patchSize_drop_tile h_in
      have h_val_sub := validPatch_filter_sub t_patch (fun t => decide (t ≠ locked_tile)) h_val
      have h_comp_sub := contiguous_edge_mutation locked_tile t_patch p h_val h_contig h_comp
      have _ih_sub := ih (t_patch.filter (fun t => decide (t ≠ locked_tile))) h_lt h_val_sub
      have h_val_other_sub := validPatch_filter_sub other (fun t => decide (t ≠ locked_tile)) h_other_val
      have h_sub_calc := euler_characteristic_subtraction locked_tile t_patch h_in d1  
      have h_euler_sub : eulerCharacteristic (t_patch.filter (fun t => decide (t ≠ locked_tile))) = 1 := by  
        rw [h_sub_calc]  
        exact h_euler
      have h_comp_other_sub := contiguous_edge_mutation locked_tile other p h_other_val h_contig h_comp_other
      have h_sub_perm := _ih_sub (other.filter (fun t => decide (t ≠ locked_tile))) (mutatePathContiguous locked_tile p) h_val_other_sub h_euler_sub h_comp_sub h_comp_other_sub
      -- Reconstruct the global patch permutation by inserting the locked boundary anchor back into both hulls
      exact perm_of_erased_perm locked_tile t_patch other h_in h_in_other d1 d2 h_sub_perm
    · -- Case 3: Non-Contiguous (Multi-Patch Disjoint Branching)
      have h_not_contig : ¬ AreEdgesContiguousInPath locked_tile p := h_contig
      have h_decomp := partitionPatchComponents locked_tile t_patch
      have h_comp_size : ∀ sub_patch ∈ partitionPatchComponents locked_tile t_patch, patchSize sub_patch < patchSize t_patch := by
        intro sub_patch h_mem
        have h_mut := non_contiguous_edge_mutation locked_tile t_patch p h_not_contig h_comp
        rcases h_mut sub_patch h_mem with ⟨sub_path, h_sub_path, h_sub_comp, h_size⟩
        exact h_size
      have h_ih_components : ∀ sub_patch ∈ partitionPatchComponents locked_tile t_patch, ∃ sub_other ∈ partitionPatchComponents locked_tile other, List.Perm sub_patch sub_other := by
        intro sub_patch h_mem
        have h_size := h_comp_size sub_patch h_mem
        have _h_rig := ih sub_patch h_size
        have h_mut := non_contiguous_edge_mutation locked_tile t_patch p h_not_contig h_comp
        rcases h_mut sub_patch h_mem with ⟨sub_path, h_sub_path, h_sub_comp, _⟩
        have h_match := find_matching_component locked_tile other p sub_path h_comp_other h_sub_path
        rcases h_match with ⟨sub_other, h_mem_other, h_comp_sub_other⟩
        have h_val_sub_patch := validPatch_of_mem_partition h_val h_mem
        have h_val_sub_other := validPatch_of_mem_partition h_other_val h_mem_other
        have h_euler_sub_path := euler_invariant_sub_patch h_euler h_mem h_sub_path h_sub_comp
        have h_perm := _h_rig h_val_sub_patch sub_other sub_path h_val_sub_other h_euler_sub_path h_sub_comp h_comp_sub_other
        exact ⟨sub_other, h_mem_other, h_perm⟩
      exact perm_of_partition_components_perm h_val h_other_val h_in h_in_other d1 d2 h_ih_components

#print axioms global_rigidity_theorem

open Lean Meta Elab Command

syntax (name := auditDeps) "audit_dependencies" : command

@[command_elab auditDeps]
def elabAuditDeps : CommandElab := fun _ => do
  let env ← getEnv
  let coreNames := [`global_rigidity_theorem, `contiguous_edge_mutation, `find_matching_component]
  for name in coreNames do
    match env.find? name with
    | some (ConstantInfo.thmInfo val) =>
      IO.println s!"--- Dependency Map for {name} ---"
      let deps := val.value.foldConsts #[] (fun n s => if s.contains n then s else s.push n)
      for dep in deps do
        let s := dep.toString
        if !s.startsWith "Mathlib" && !s.startsWith "Lean" && !s.startsWith "Nat" && !s.startsWith "List" &&
           !s.startsWith "Eq" && !s.startsWith "Int" && !s.startsWith "OfNat" && !s.startsWith "CommRing" &&
           !s.startsWith "Ring" && !s.startsWith "Zero" && !s.startsWith "One" && !s.startsWith "Add" &&
           !s.startsWith "Neg" && !s.startsWith "Sub" && !s.startsWith "Mul" && !s.startsWith "HAdd" &&
           !s.startsWith "HMul" && !s.startsWith "HPow" && !s.startsWith "Monoid" && !s.startsWith "Semiring" &&
           !s.startsWith "Decidable" && !s.startsWith "congr" && !s.startsWith "rfl" && !s.startsWith "id" &&
           !s.startsWith "inferInstance" && !s.startsWith "Distrib" && !s.startsWith "CommSemiring" &&
           !s.startsWith "NonAssocSemiring" && !s.startsWith "AddCommMonoid" && !s.startsWith "AddMonoid" &&
           !s.startsWith "AddCommGroup" && !s.startsWith "SubtractionMonoid" && !s.startsWith "SubtractionCommMonoid" &&
           !s.startsWith "SubNegZeroMonoid" && !s.startsWith "NegZeroClass" && !s.startsWith "MulZeroClass" then
          IO.println s!"  => Depends on: {dep}"
    | _ => IO.println s!"Declaration {name} not found or is not a theorem."

audit_dependencies

