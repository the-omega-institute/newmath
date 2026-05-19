import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessLedgerReadbackTotality [AskSetup] [PackageSetup]
    {Q B S K H C P N selected : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (hsame selected Q ∨ hsame selected B ∨ hsame selected S ∨ hsame selected K ∨
        hsame selected H ∨ hsame selected C ∨ hsame selected P ∨ hsame selected N) ->
      PkgSig bundle N pkg ->
        SemanticNameCert
          (fun row : BHist =>
            hsame row selected ∧
              (hsame selected Q ∨ hsame selected B ∨ hsame selected S ∨
                hsame selected K ∨ hsame selected H ∨ hsame selected C ∨
                  hsame selected P ∨ hsame selected N) ∧
                ∃ packet : CauchyWitnessLedgerUp,
                  packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
          (fun row : BHist => hsame row selected ∧ PkgSig bundle N pkg)
          (fun row : BHist =>
            (hsame row Q ∨ hsame row B ∨ hsame row S ∨ hsame row K ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N) ∧
              PkgSig bundle N pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert
  intro selectedDisplayed namePkg
  have packetWitness :
      ∃ packet : CauchyWitnessLedgerUp,
        packet = CauchyWitnessLedgerUp.mk Q B S K H C P N :=
    Exists.intro (CauchyWitnessLedgerUp.mk Q B S K H C P N) rfl
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro selected ⟨hsame_refl selected, selectedDisplayed, packetWitness⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left, source.right.left,
            source.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
    ledger_sound := by
      intro _row source
      cases source.right.left with
      | inl sameQ =>
          exact ⟨Or.inl (hsame_trans source.left sameQ), namePkg⟩
      | inr rest =>
          cases rest with
          | inl sameB =>
              exact ⟨Or.inr (Or.inl (hsame_trans source.left sameB)), namePkg⟩
          | inr rest =>
              cases rest with
              | inl sameS =>
                  exact
                    ⟨Or.inr (Or.inr (Or.inl (hsame_trans source.left sameS))),
                      namePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameK =>
                      exact
                        ⟨Or.inr
                            (Or.inr (Or.inr (Or.inl (hsame_trans source.left sameK)))),
                          namePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameH =>
                          exact
                            ⟨Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inl (hsame_trans source.left sameH))))),
                              namePkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameC =>
                              exact
                                ⟨Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans source.left sameC)))))),
                                  namePkg⟩
                          | inr rest =>
                              cases rest with
                              | inl sameP =>
                                  exact
                                    ⟨Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans source.left sameP))))))),
                                      namePkg⟩
                              | inr sameN =>
                                  exact
                                    ⟨Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (hsame_trans source.left sameN))))))),
                                      namePkg⟩
  }

end BEDC.Derived.CauchyWitnessLedgerUp
