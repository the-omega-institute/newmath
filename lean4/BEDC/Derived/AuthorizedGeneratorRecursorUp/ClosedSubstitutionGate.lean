import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorClosedSubstitutionGate
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I -> UnaryHistory E -> UnaryHistory B -> UnaryHistory D ->
      UnaryHistory O -> UnaryHistory A -> UnaryHistory C -> UnaryHistory N ->
        Cont I E branchRead -> Cont branchRead D descentRead ->
          Cont descentRead O outputRead -> Cont outputRead C publicRead ->
            PkgSig bundle P pkg ->
              UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                UnaryHistory outputRead ∧ UnaryHistory publicRead ∧
                  Cont I E branchRead ∧ Cont branchRead D descentRead ∧
                    Cont descentRead O outputRead ∧ Cont outputRead C publicRead ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row N ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row N ∧ Cont I E branchRead ∧
                            Cont branchRead D descentRead ∧
                              Cont descentRead O outputRead ∧
                                Cont outputRead C publicRead)
                        (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro unaryI unaryE unaryB unaryD unaryO _unaryA unaryC unaryN routeBranch
    routeDescent routeOutput routePublic pkgSig
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryI unaryE routeBranch
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary unaryD routeDescent
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary unaryO routeOutput
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary unaryC routePublic
  have sourceN : (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row N ∧ Cont I E branchRead ∧ Cont branchRead D descentRead ∧
            Cont descentRead O outputRead ∧ Cont outputRead C publicRead)
        (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
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
      exact ⟨source.left, routeBranch, routeDescent, routeOutput, routePublic⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgSig⟩
  }
  exact
    ⟨branchReadUnary, descentReadUnary, outputReadUnary, publicReadUnary, routeBranch,
      routeDescent, routeOutput, routePublic, cert⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
