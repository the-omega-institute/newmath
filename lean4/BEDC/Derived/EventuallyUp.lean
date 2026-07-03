import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EventuallyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EventuallyCarrier [AskSetup] [PackageSetup]
    (D W T S R A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory T ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem EventuallyCarrier_directed_tail_handoff [AskSetup] [PackageSetup]
    {D W T S R A H C P N streamRead realRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier : EventuallyCarrier D W T S R A H C P N bundle pkg)
    (streamRoute : Cont T S streamRead) (realRoute : Cont R A realRead)
    (nameRoute : Cont C N nameRead) :
    SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row S ∨ hsame row R ∨
            hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist => UnaryHistory row ∧ Cont C N nameRead ∧ PkgSig bundle N pkg)
        hsame ∧
      UnaryHistory streamRead ∧ UnaryHistory realRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  have dUnary : UnaryHistory D := carrier.left
  have wUnary : UnaryHistory W := carrier.right.left
  have tUnary : UnaryHistory T := carrier.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.left
  have rUnary : UnaryHistory R := carrier.right.right.right.right.left
  have aUnary : UnaryHistory A := carrier.right.right.right.right.right.left
  have cUnary : UnaryHistory C := carrier.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    carrier.right.right.right.right.right.right.right.right.left
  have nPkg : PkgSig bundle N pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed tUnary sUnary streamRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed rUnary aUnary realRoute
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed cUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row T ∨ hsame row S ∨ hsame row R ∨
              hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ Cont C N nameRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro N ⟨hsame_refl N, nUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, nameRoute, nPkg⟩
  }
  exact ⟨cert, streamReadUnary, realReadUnary, nameReadUnary⟩

theorem EventuallyCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {D W T S R A H C P N streamRead realRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EventuallyCarrier D W T S R A H C P N bundle pkg ->
      Cont T S streamRead -> Cont R A realRead -> Cont C N nameRead ->
        UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory T ∧ UnaryHistory S ∧
          UnaryHistory R ∧ UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧
            UnaryHistory N ∧ UnaryHistory streamRead ∧ UnaryHistory realRead ∧
              UnaryHistory nameRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                Cont T S streamRead ∧ Cont R A realRead ∧ Cont C N nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig Cont UnaryHistory
  intro carrier streamRoute realRoute nameRoute
  have dUnary : UnaryHistory D := carrier.left
  have wUnary : UnaryHistory W := carrier.right.left
  have tUnary : UnaryHistory T := carrier.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.left
  have rUnary : UnaryHistory R := carrier.right.right.right.right.left
  have aUnary : UnaryHistory A := carrier.right.right.right.right.right.left
  have hUnary : UnaryHistory H := carrier.right.right.right.right.right.right.left
  have cUnary : UnaryHistory C := carrier.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    carrier.right.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have nPkg : PkgSig bundle N pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed tUnary sUnary streamRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed rUnary aUnary realRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed cUnary nUnary nameRoute
  exact
    ⟨dUnary, wUnary, tUnary, sUnary, rUnary, aUnary, hUnary, cUnary, nUnary,
      streamUnary, realUnary, nameUnary, pPkg, nPkg, streamRoute, realRoute, nameRoute⟩

end BEDC.Derived.EventuallyUp
