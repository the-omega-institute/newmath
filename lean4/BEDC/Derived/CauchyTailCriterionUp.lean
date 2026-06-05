import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyTailCriterionCarrier [AskSetup] [PackageSetup]
    (S D R M E F B H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory M ∧
    UnaryHistory E ∧ UnaryHistory F ∧ UnaryHistory B ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg

theorem CauchyTailCriterionRealSealHandoff [AskSetup] [PackageSetup]
    {S D R M E F B H C P N tailRead regularRead sealRead fastRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailCriterionCarrier S D R M E F B H C P N bundle pkg →
      Cont S D tailRead →
        Cont tailRead R regularRead →
          Cont regularRead E sealRead →
            Cont sealRead F fastRead →
              PkgSig bundle fastRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row fastRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row M ∨
                        hsame row E ∨ hsame row F ∨ hsame row B ∨ hsame row fastRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S D tailRead ∧ Cont tailRead R regularRead ∧
                        Cont regularRead E sealRead ∧ Cont sealRead F fastRead ∧
                          PkgSig bundle fastRead pkg)
                    hsame ∧
                  UnaryHistory tailRead ∧ UnaryHistory regularRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory fastRead := by
  -- BEDC touchpoint anchor: CauchyTailCriterionCarrier BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier sourceDyadicTail tailRegular regularSeal sealFast fastPkg
  obtain ⟨sourceUnary, dyadicUnary, regularUnary, _modulusUnary, endpointUnary,
    fastUnary, _tailLedgerUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _provenancePkg, _namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary dyadicUnary sourceDyadicTail
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed tailUnary regularUnary tailRegular
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary endpointUnary regularSeal
  have fastReadUnary : UnaryHistory fastRead :=
    unary_cont_closed sealReadUnary fastUnary sealFast
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row fastRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row D ∨ hsame row R ∨ hsame row M ∨
              hsame row E ∨ hsame row F ∨ hsame row B ∨ hsame row fastRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S D tailRead ∧ Cont tailRead R regularRead ∧
              Cont regularRead E sealRead ∧ Cont sealRead F fastRead ∧
                PkgSig bundle fastRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro fastRead ⟨hsame_refl fastRead, fastReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceDyadicTail, tailRegular, regularSeal, sealFast,
          fastPkg⟩
  }
  exact ⟨cert, tailUnary, regularReadUnary, sealReadUnary, fastReadUnary⟩

end BEDC.Derived.CauchyTailCriterionUp
