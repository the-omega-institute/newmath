import BEDC.Derived.FiniteCauchyTailHandoffUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteCauchyTailHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteCauchyTailHandoffPacket [AskSetup] [PackageSetup]
    (R W D M S Z H K P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory M ∧
    UnaryHistory S ∧ UnaryHistory Z ∧ UnaryHistory H ∧ UnaryHistory K ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont W D M ∧ Cont M S Z ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem FiniteCauchyTailHandoffNameCertObligations [AskSetup] [PackageSetup]
    {R W D M S Z H K P N modulusRead selectorRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteCauchyTailHandoffPacket R W D M S Z H K P N bundle pkg →
      Cont R W modulusRead →
        Cont modulusRead D selectorRead →
          Cont selectorRead Z sealedRead →
            PkgSig bundle sealedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row M ∨
                      hsame row S ∨ hsame row Z ∨ hsame row H ∨ hsame row K ∨
                        hsame row P ∨ hsame row N ∨ hsame row sealedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R W modulusRead ∧
                      Cont modulusRead D selectorRead ∧ Cont selectorRead Z sealedRead ∧
                        PkgSig bundle sealedRead pkg)
                  hsame ∧
                UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                  UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet readWindow modulusSelector selectorSeal sealPkg
  obtain ⟨readUnary, windowUnary, dyadicUnary, _modulusUnary, _selectorUnary, sealRowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _windowDyadicModulus,
    _modulusSelectorSeal, _provenancePkg, _namePkg⟩ := packet
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed readUnary windowUnary readWindow
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary dyadicUnary modulusSelector
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed selectorUnary sealRowUnary selectorSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row) sealedRead := by
    exact ⟨hsame_refl sealedRead, sealedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row M ∨ hsame row S ∨
              hsame row Z ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
                hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W modulusRead ∧
              Cont modulusRead D selectorRead ∧ Cont selectorRead Z sealedRead ∧
                PkgSig bundle sealedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead sourceSeal
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, readWindow, modulusSelector, selectorSeal, sealPkg⟩
  }
  exact ⟨cert, modulusUnary, selectorUnary, sealedUnary⟩

end BEDC.Derived.FiniteCauchyTailHandoffUp
