import BEDC.Derived.ScienceBridgeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ScienceBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ScienceBridgeStandardAuditHandoff [AskSetup] [PackageSetup]
    {R O A T B G F H C P N recordsRead bridgeAuditRead truthRead failureRead
      replayRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ScienceBridgeUp →
      UnaryHistory R → UnaryHistory B → UnaryHistory G → UnaryHistory T →
        UnaryHistory F → UnaryHistory H → UnaryHistory C → UnaryHistory N →
          Cont R B recordsRead → Cont recordsRead G bridgeAuditRead →
            Cont bridgeAuditRead T truthRead → Cont truthRead F failureRead →
              Cont failureRead H replayRead → Cont replayRead C publicRead →
                PkgSig bundle P pkg →
                  SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row R ∨ hsame row B ∨ hsame row G ∨ hsame row T ∨
                        hsame row F ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont R B recordsRead ∧
                        Cont recordsRead G bridgeAuditRead ∧
                          Cont bridgeAuditRead T truthRead ∧
                            Cont truthRead F failureRead ∧
                              Cont failureRead H replayRead ∧
                                Cont replayRead C publicRead ∧ PkgSig bundle P pkg)
                    hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: ScienceBridgeUp BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _scienceBridge unaryR unaryB unaryG unaryT unaryF unaryH unaryC _unaryN
    recordsRoute bridgeAuditRoute truthRoute failureRoute replayRoute publicRoute packageRead
  have _objectRow : BHist := O
  have _auditRow : BHist := A
  have recordsUnary : UnaryHistory recordsRead :=
    unary_cont_closed unaryR unaryB recordsRoute
  have bridgeAuditUnary : UnaryHistory bridgeAuditRead :=
    unary_cont_closed recordsUnary unaryG bridgeAuditRoute
  have truthUnary : UnaryHistory truthRead :=
    unary_cont_closed bridgeAuditUnary unaryT truthRoute
  have failureUnary : UnaryHistory failureRead :=
    unary_cont_closed truthUnary unaryF failureRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed failureUnary unaryH replayRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed replayUnary unaryC publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row R ∨ hsame row B ∨ hsame row G ∨ hsame row T ∨ hsame row F ∨
            hsame row publicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont R B recordsRead ∧
            Cont recordsRead G bridgeAuditRead ∧ Cont bridgeAuditRead T truthRead ∧
              Cont truthRead F failureRead ∧ Cont failureRead H replayRead ∧
                Cont replayRead C publicRead ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, recordsRoute, bridgeAuditRoute, truthRoute, failureRoute,
          replayRoute, publicRoute, packageRead⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.ScienceBridgeUp
