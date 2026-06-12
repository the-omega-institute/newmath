import BEDC.Derived.FiniteWindowObserverUp.InscriptionHandoff
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWindowObserverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteWindowObserverLedgerNonescape [AskSetup] [PackageSetup]
    {O F I K D H C P N selectRead checkerRead acceptedRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowObserverCarrier O F I K D H C P N bundle pkg →
      Cont O F selectRead →
        Cont selectRead I checkerRead →
          Cont checkerRead K acceptedRead →
            Cont acceptedRead D handoffRead →
              PkgSig bundle handoffRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row O ∨ hsame row F ∨ hsame row I ∨ hsame row K ∨
                        hsame row D ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row handoffRead)
                    (fun row : BHist =>
                      hsame row handoffRead ∧ PkgSig bundle handoffRead pkg)
                    hsame ∧
                  UnaryHistory selectRead ∧ UnaryHistory checkerRead ∧
                    UnaryHistory acceptedRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier selectRoute checkerRoute acceptedRoute handoffRoute handoffPkg
  obtain ⟨observerUnary, windowUnary, inscriptionUnary, checkerUnary, downstreamUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary, _windowRoute,
    _provenanceRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have selectUnary : UnaryHistory selectRead :=
    unary_cont_closed observerUnary windowUnary selectRoute
  have checkerReadUnary : UnaryHistory checkerRead :=
    unary_cont_closed selectUnary inscriptionUnary checkerRoute
  have acceptedReadUnary : UnaryHistory acceptedRead :=
    unary_cont_closed checkerReadUnary checkerUnary acceptedRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed acceptedReadUnary downstreamUnary handoffRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row O ∨ hsame row F ∨ hsame row I ∨ hsame row K ∨ hsame row D ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row handoffRead)
        (fun row : BHist => hsame row handoffRead ∧ PkgSig bundle handoffRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, handoffPkg⟩
  }
  exact ⟨cert, selectUnary, checkerReadUnary, acceptedReadUnary, handoffReadUnary⟩

end BEDC.Derived.FiniteWindowObserverUp
