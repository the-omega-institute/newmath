import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TheorySelfClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TheorySelfClassifier_nonescape [AskSetup] [PackageSetup]
    {G E R Pu A L H C Q N commitmentRead ledgerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G ->
      UnaryHistory E ->
        UnaryHistory R ->
          UnaryHistory Pu ->
            UnaryHistory A ->
              UnaryHistory L ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory Q ->
                      UnaryHistory N ->
                        Cont G E commitmentRead ->
                          Cont commitmentRead R ledgerRead ->
                            Cont ledgerRead L publicRead ->
                              PkgSig bundle Q pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row publicRead /\ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row G \/ hsame row E \/ hsame row R \/
                                          hsame row Pu \/ hsame row A \/ hsame row L \/
                                            hsame row H \/ hsame row C \/ hsame row Q \/
                                              hsame row N \/ hsame row commitmentRead \/
                                                hsame row ledgerRead \/ hsame row publicRead)
                                      (fun row : BHist =>
                                        UnaryHistory row /\ Cont G E commitmentRead /\
                                          Cont commitmentRead R ledgerRead /\
                                            Cont ledgerRead L publicRead /\
                                              PkgSig bundle Q pkg /\ PkgSig bundle N pkg)
                                      hsame /\
                                    UnaryHistory commitmentRead /\ UnaryHistory ledgerRead /\
                                      UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryG unaryE unaryR _unaryPu _unaryA unaryL _unaryH _unaryC _unaryQ _unaryN
    commitmentRoute ledgerRoute publicRoute pkgQ pkgN
  have commitmentUnary : UnaryHistory commitmentRead :=
    unary_cont_closed unaryG unaryE commitmentRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed commitmentUnary unaryR ledgerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary unaryL publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row G \/ hsame row E \/ hsame row R \/ hsame row Pu \/
              hsame row A \/ hsame row L \/ hsame row H \/ hsame row C \/
                hsame row Q \/ hsame row N \/ hsame row commitmentRead \/
                  hsame row ledgerRead \/ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row /\ Cont G E commitmentRead /\
              Cont commitmentRead R ledgerRead /\ Cont ledgerRead L publicRead /\
                PkgSig bundle Q pkg /\ PkgSig bundle N pkg)
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
      right
      right
      right
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
      exact ⟨source.right, commitmentRoute, ledgerRoute, publicRoute, pkgQ, pkgN⟩
  }
  exact ⟨cert, commitmentUnary, ledgerUnary, publicUnary⟩

end BEDC.Derived.TheorySelfClassifierUp
