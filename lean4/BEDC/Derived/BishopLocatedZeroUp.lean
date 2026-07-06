import BEDC.Derived.BishopLocatedZeroUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopLocatedZeroUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopLocatedZeroCarrier [AskSetup] [PackageSetup]
    (B M S Q A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory B ∧ UnaryHistory M ∧ UnaryHistory S ∧ UnaryHistory Q ∧
    UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BishopLocatedZeroNameCertObligations [AskSetup] [PackageSetup]
    {B M S Q A H C P N bisectionRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopLocatedZeroCarrier B M S Q A H C P N bundle pkg →
      Cont B M bisectionRead →
        Cont bisectionRead A sealRead →
          Cont sealRead N namedRead →
            PkgSig bundle namedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨
                      hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B M bisectionRead ∧
                      Cont bisectionRead A sealRead ∧ Cont sealRead N namedRead ∧
                        PkgSig bundle namedRead pkg)
                  hsame ∧
                UnaryHistory bisectionRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier bisectionRoute sealRoute namedRoute namedPkg
  obtain ⟨unaryB, unaryM, _unaryS, _unaryQ, unaryA, _unaryH, _unaryC, _unaryP,
    unaryN, _provenancePkg, _localNamePkg⟩ := carrier
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed unaryB unaryM bisectionRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed bisectionUnary unaryA sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨
              hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B M bisectionRead ∧
              Cont bisectionRead A sealRead ∧ Cont sealRead N namedRead ∧
                PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bisectionRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, bisectionUnary, sealUnary, namedUnary⟩

end BEDC.Derived.BishopLocatedZeroUp
