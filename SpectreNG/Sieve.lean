import SpectreNG.Topology

open LatticePoint

/-- Helper function returning the uniquely matching layout (patch) for each of the 22 stable paths. -/
def getPathPatch : Path → Patch
  | [Turn.r90, Turn.r60, Turn.l90, Turn.r60, Turn.l90] => [⟨⟨0, 0, 0, 0⟩, 0⟩, ⟨⟨1, 0, 0, -1⟩, 7⟩]
  | [Turn.r90, Turn.r60, Turn.l90, Turn.l60, Turn.straight] => [⟨⟨0, 0, 0, 0⟩, 0⟩, ⟨⟨2, 0, 0, 0⟩, 6⟩]
  | [Turn.r90, Turn.l60, Turn.r90, Turn.l60, Turn.l90] => [⟨⟨0, 0, 0, 0⟩, 0⟩, ⟨⟨2, 2, -2, -2⟩, 11⟩]
  | [Turn.r90, Turn.l60, Turn.straight, Turn.l60, Turn.r90] => [⟨⟨0, 0, 0, 0⟩, 0⟩, ⟨⟨2, 1, 1, -1⟩, 5⟩]
  | [Turn.r90, Turn.l60, Turn.l90, Turn.r60, Turn.l90] => [⟨⟨1, 1, 1, -2⟩, 0⟩]
  | [Turn.r90, Turn.l60, Turn.l90, Turn.l60, Turn.r90] => [⟨⟨-1, 2, 2, -1⟩, 4⟩]
  | [Turn.r60, Turn.r90, Turn.r60, Turn.l90, Turn.r60] => [⟨⟨0, 0, 0, 1⟩, 9⟩, ⟨⟨2, -1, -1, 0⟩, 5⟩]
  | [Turn.r60, Turn.r90, Turn.r60, Turn.l90, Turn.l60] => [⟨⟨0, 0, 0, 1⟩, 9⟩, ⟨⟨3, 0, -2, 0⟩, 4⟩]
  | [Turn.r60, Turn.r90, Turn.l60, Turn.r90, Turn.l60] => [⟨⟨0, 0, 0, 1⟩, 9⟩, ⟨⟨1, 0, -2, -2⟩, 9⟩]
  | [Turn.r60, Turn.r90, Turn.l60, Turn.straight, Turn.l60] => [⟨⟨0, 0, 0, 1⟩, 9⟩, ⟨⟨4, 0, -2, -1⟩, 3⟩]
  | [Turn.r60, Turn.l90, Turn.r60, Turn.l90, Turn.l60] => [⟨⟨1, 0, 0, 0⟩, 10⟩]
  | [Turn.r60, Turn.l90, Turn.l60, Turn.straight, Turn.l60] => [⟨⟨0, 0, 0, 1⟩, 9⟩]
  | [Turn.straight, Turn.l60, Turn.r90, Turn.l60, Turn.l90] => [⟨⟨0, 1, 1, 1⟩, 6⟩]
  | [Turn.l60, Turn.r90, Turn.l60, Turn.l90, Turn.r60] => [⟨⟨0, 2, 2, -1⟩, 2⟩]
  | [Turn.l60, Turn.r90, Turn.l60, Turn.l90, Turn.l60] => [⟨⟨-1, 1, 1, 1⟩, 6⟩]
  | [Turn.l60, Turn.straight, Turn.l60, Turn.r90, Turn.l60] => [⟨⟨0, -1, 1, 2⟩, 8⟩]
  | [Turn.l60, Turn.l90, Turn.r60, Turn.l90, Turn.r60] => [⟨⟨1, -1, 1, 1⟩, 3⟩]
  | [Turn.l60, Turn.l90, Turn.l60, Turn.r90, Turn.l60] => [⟨⟨-1, -2, 2, 0⟩, 7⟩]
  | [Turn.l90, Turn.r60, Turn.l90, Turn.r60, Turn.l90] => [⟨⟨1, 0, 0, 1⟩, 1⟩]
  | [Turn.l90, Turn.r60, Turn.l90, Turn.l60, Turn.straight] => [⟨⟨0, 0, 0, 0⟩, 0⟩]
  | [Turn.l90, Turn.l60, Turn.r90, Turn.l60, Turn.l90] => [⟨⟨0, -2, 2, 2⟩, 5⟩]
  | [Turn.l90, Turn.l60, Turn.straight, Turn.l60, Turn.r90] => [⟨⟨0, -1, -1, 1⟩, 11⟩]
  | _ => []


/-- Computable check function verifySievePlateau that maps over the list,
    evaluating isValidPatchBool and completesPathBool against their matching layouts. -/
def verifySievePlateau (paths : List Path) : Bool :=
  paths.all (fun p =>
    let patch := getPathPatch p
    isValidPatchBool patch && completesPathBool patch p
  )

/-- Reflective validation lemma establishing that all 22 stable plateau paths are verified. -/
theorem stable_plateau_verified : verifySievePlateau stablePaths = true := by
  rfl


theorem reflect_sieve_lock (p : Path) (h : verify_sieve_window p = true) :  
  UniquelyDetermined p := by  
  have h_mem := of_decide_eq_true h
  have h_len : p.length = 5 := by
    dsimp [stablePaths] at h_mem
    simp only [List.mem_cons, List.not_mem_nil] at h_mem
    rcases h_mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · cases h_false
  exact aperiodic_holography_lock p h_len h
