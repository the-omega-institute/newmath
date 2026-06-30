import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_ledger_refusal_totality [AskSetup] [PackageSetup]
    {Z S M R Q H C P N refusalRead publicRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont M Q refusalRead →
        Cont refusalRead N publicRead →
          PkgSig bundle P pkg →
            PkgSig bundle N pkg →
              SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                    Cont refusalRead N publicRead)
                hsame ∧ UnaryHistory refusalRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet refusalRoute publicRoute provenancePkg localNamePkg
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport appendUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryM unaryQ refusalRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed refusalUnary unaryN publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
            hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row publicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
            Cont refusalRead N publicRead)
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg, publicRoute⟩
  }
  exact ⟨cert, refusalUnary, publicUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
