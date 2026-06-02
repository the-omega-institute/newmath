import BEDC.Derived.RegularCauchyInterleavingUp

namespace BEDC.Derived.RegularCauchyInterleavingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyInterleavingPacket_even_odd_subsequence_seal [AskSetup]
    [PackageSetup]
    {leftName rightName leftSchedule rightSchedule selector modulus leftSeal rightSeal
      interleavedSeal transport routes provenance nameCert endpoint evenRead oddRead
      selectedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavingPacket leftName rightName leftSchedule rightSchedule selector
        modulus leftSeal rightSeal interleavedSeal transport routes provenance nameCert endpoint
        bundle pkg ->
      Cont selector leftSchedule evenRead ->
        Cont selector rightSchedule oddRead ->
          Cont evenRead oddRead selectedSeal ->
            PkgSig bundle selectedSeal pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row evenRead ∨ hsame row oddRead ∨ hsame row selectedSeal) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row leftName ∨ hsame row rightName ∨ hsame row leftSchedule ∨
                      hsame row rightSchedule ∨ hsame row selector ∨ hsame row modulus ∨
                        hsame row evenRead ∨ hsame row oddRead ∨ hsame row selectedSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont selector leftSchedule evenRead ∧
                      Cont selector rightSchedule oddRead ∧ Cont evenRead oddRead selectedSeal ∧
                        PkgSig bundle selectedSeal pkg)
                  hsame ∧
                UnaryHistory evenRead ∧ UnaryHistory oddRead ∧
                  UnaryHistory selectedSeal := by
  -- BEDC touchpoint anchor: RegularCauchyInterleavingPacket BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet evenRoute oddRoute selectedRoute selectedPkg
  obtain ⟨leftNameUnary, rightNameUnary, leftScheduleUnary, rightScheduleUnary, selectorUnary,
    _modulusUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary,
    _leftSealRoute, _rightSealRoute, _interleavedRoute, _endpointRoute, _endpointPkg⟩ := packet
  have evenUnary : UnaryHistory evenRead :=
    unary_cont_closed selectorUnary leftScheduleUnary evenRoute
  have oddUnary : UnaryHistory oddRead :=
    unary_cont_closed selectorUnary rightScheduleUnary oddRoute
  have selectedUnary : UnaryHistory selectedSeal :=
    unary_cont_closed evenUnary oddUnary selectedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row evenRead ∨ hsame row oddRead ∨ hsame row selectedSeal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row leftName ∨ hsame row rightName ∨ hsame row leftSchedule ∨
              hsame row rightSchedule ∨ hsame row selector ∨ hsame row modulus ∨
                hsame row evenRead ∨ hsame row oddRead ∨ hsame row selectedSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont selector leftSchedule evenRead ∧
              Cont selector rightSchedule oddRead ∧ Cont evenRead oddRead selectedSeal ∧
                PkgSig bundle selectedSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro selectedSeal ⟨Or.inr (Or.inr (hsame_refl selectedSeal)), selectedUnary⟩
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
        constructor
        · cases source.left with
          | inl sameEven =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameEven)
          | inr tail =>
              cases tail with
              | inl sameOdd =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameOdd))
              | inr sameSelected =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSelected))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameEven =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameEven))))))
      | inr tail =>
          cases tail with
          | inl sameOdd =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameOdd)))))))
          | inr sameSelected =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSelected)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, evenRoute, oddRoute, selectedRoute, selectedPkg⟩
  }
  exact ⟨cert, evenUnary, oddUnary, selectedUnary⟩

end BEDC.Derived.RegularCauchyInterleavingUp
