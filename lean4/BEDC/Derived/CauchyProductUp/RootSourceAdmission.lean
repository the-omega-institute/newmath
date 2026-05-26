import BEDC.Derived.CauchyProductUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_source_admission [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont windowA windowB transport ->
        PkgSig bundle sourceRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row sourceA ∨ hsame row sourceB ∨ hsame row windowA ∨
                  hsame row windowB ∨ hsame row observationA ∨ hsame row observationB)
              (fun row : BHist =>
                hsame row sourceA ∨ hsame row sourceB ∨ hsame row windowA ∨
                  hsame row windowB ∨ hsame row observationA ∨ hsame row observationB)
              (fun row : BHist =>
                PkgSig bundle sourceRead pkg ∧
                  (hsame row sourceA ∨ hsame row sourceB ∨ hsame row windowA ∨
                    hsame row windowB ∨ hsame row observationA ∨ hsame row observationB))
              hsame ∧
            UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
              UnaryHistory windowB ∧ UnaryHistory observationA ∧ UnaryHistory observationB ∧
                Cont observationA observationB product := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro packet _windowTransportInput sourceReadPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, _ledgerUnary,
    _windowTransport, productRoute, _classifierRoute, _namePkg⟩ := packet
  have sourceAAtSource :
      hsame sourceA sourceA ∨ hsame sourceA sourceB ∨ hsame sourceA windowA ∨
        hsame sourceA windowB ∨ hsame sourceA observationA ∨ hsame sourceA observationB :=
    Or.inl (hsame_refl sourceA)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row sourceA ∨ hsame row sourceB ∨ hsame row windowA ∨
              hsame row windowB ∨ hsame row observationA ∨ hsame row observationB)
          (fun row : BHist =>
            hsame row sourceA ∨ hsame row sourceB ∨ hsame row windowA ∨
              hsame row windowB ∨ hsame row observationA ∨ hsame row observationB)
          (fun row : BHist =>
            PkgSig bundle sourceRead pkg ∧
              (hsame row sourceA ∨ hsame row sourceB ∨ hsame row windowA ∨
                hsame row windowB ∨ hsame row observationA ∨ hsame row observationB))
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sourceA sourceAAtSource
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
          intro _row _other sameRows sourceRow
          cases sourceRow with
          | inl rowSourceA =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) rowSourceA)
          | inr tail =>
              cases tail with
              | inl rowSourceB =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowSourceB))
              | inr tail =>
                  cases tail with
                  | inl rowWindowA =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowWindowA)))
                  | inr tail =>
                      cases tail with
                      | inl rowWindowB =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) rowWindowB))))
                      | inr tail =>
                          cases tail with
                          | inl rowObservationA =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows)
                                          rowObservationA)))))
                          | inr rowObservationB =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (hsame_trans (hsame_symm sameRows)
                                          rowObservationB)))))
      }
      pattern_sound := by
        intro _row sourceRow
        exact sourceRow
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceReadPkg, sourceRow⟩
    }
  exact
    ⟨cert, sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, observationAUnary,
      observationBUnary, productRoute⟩

end BEDC.Derived.CauchyProductUp
