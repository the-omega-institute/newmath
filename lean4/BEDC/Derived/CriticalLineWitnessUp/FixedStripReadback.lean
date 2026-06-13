import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_source_refusal_readback_certificate
    {Z S M R Q H C P N zeroRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead Q refusalRead ->
          SemanticNameCert
              (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row refusalRead)
              (fun row : BHist => hsame row refusalRead ∧ Cont zeroRead Q refusalRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory zeroRead ∧
              UnaryHistory refusalRead ∧ hsame H (append Z S) ∧ Cont Z S zeroRead ∧
                Cont zeroRead Q refusalRead ∧ Cont M R Q ∧ Cont Q H C ∧
                  Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryZeroRead : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed unaryZeroRead unaryQ refusalRoute
  have sourceAtRefusal :
      hsame refusalRead refusalRead ∧ UnaryHistory refusalRead :=
    ⟨hsame_refl refusalRead, unaryRefusalRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row refusalRead)
          (fun row : BHist => hsame row refusalRead ∧ Cont zeroRead Q refusalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceAtRefusal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryZeroRead, unaryRefusalRead, sameH, zeroRoute,
      refusalRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_zero_strip_modulus_separation_certificate
    {Z S M R Q H C P N zeroRead modulusRead separatedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont M R modulusRead ->
          Cont zeroRead modulusRead separatedRead ->
            SemanticNameCert
                (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row separatedRead)
                (fun row : BHist =>
                  hsame row separatedRead ∧ Cont zeroRead modulusRead separatedRead)
                hsame ∧
              UnaryHistory zeroRead ∧ UnaryHistory modulusRead ∧ UnaryHistory separatedRead ∧
                hsame H (append Z S) ∧ Cont Z S zeroRead ∧ Cont M R modulusRead ∧
                  Cont zeroRead modulusRead separatedRead ∧ Cont M R Q ∧ Cont Q H C ∧
                    Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute modulusRoute separatedRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryZeroRead : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unarySeparatedRead : UnaryHistory separatedRead :=
    unary_cont_closed unaryZeroRead unaryModulusRead separatedRoute
  have sourceAtSeparated :
      hsame separatedRead separatedRead ∧ UnaryHistory separatedRead :=
    ⟨hsame_refl separatedRead, unarySeparatedRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row separatedRead)
          (fun row : BHist =>
            hsame row separatedRead ∧ Cont zeroRead modulusRead separatedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro separatedRead sourceAtSeparated
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, separatedRoute⟩
  }
  exact
    ⟨cert, unaryZeroRead, unaryModulusRead, unarySeparatedRead, sameH, zeroRoute,
      modulusRoute, separatedRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
