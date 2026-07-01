import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.DyadicErrorBudgetUp.TasteGate

namespace BEDC.Derived.DyadicErrorBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicErrorBudgetCarrier [AskSetup] [PackageSetup]
    (Q A B S WX WY DX DY DZ RX RY T H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory Q ∧ UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory S ∧
    UnaryHistory WX ∧ UnaryHistory WY ∧ UnaryHistory DX ∧ UnaryHistory DY ∧
      UnaryHistory DZ ∧ UnaryHistory RX ∧ UnaryHistory RY ∧ UnaryHistory T ∧
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
          PkgSig bundle P pkg

theorem DyadicErrorBudgetCarrier_triangle_accounting [AskSetup] [PackageSetup]
    {Q A B S WX WY DX DY DZ RX RY T H C P N leftRead rightRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicErrorBudgetCarrier Q A B S WX WY DX DY DZ RX RY T H C P N bundle pkg →
      Cont WX DX leftRead →
        Cont WY DY rightRead →
          Cont DZ T tailRead →
            PkgSig bundle tailRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Q ∨ hsame row A ∨ hsame row B ∨ hsame row S ∨
                      hsame row WX ∨ hsame row WY ∨ hsame row DX ∨ hsame row DY ∨
                        hsame row DZ ∨ hsame row RX ∨ hsame row RY ∨ hsame row T ∨
                          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row leftRead ∨ hsame row rightRead ∨
                              hsame row tailRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont WX DX leftRead ∧ Cont WY DY rightRead ∧
                      Cont DZ T tailRead ∧ PkgSig bundle tailRead pkg)
                  hsame ∧
                UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                  UnaryHistory tailRead := by
  -- BEDC touchpoint anchor: DyadicErrorBudgetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier routeLeft routeRight routeTail tailPkg
  obtain ⟨_unaryQ, _unaryA, _unaryB, _unaryS, unaryWX, unaryWY, unaryDX, unaryDY,
    unaryDZ, _unaryRX, _unaryRY, unaryT, _unaryH, _unaryC, _unaryP, _unaryN,
    _provenancePkg⟩ := carrier
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed unaryWX unaryDX routeLeft
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed unaryWY unaryDY routeRight
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed unaryDZ unaryT routeTail
  have sourceTail :
      (fun row : BHist => hsame row tailRead ∧ UnaryHistory row) tailRead := by
    exact ⟨hsame_refl tailRead, tailUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row A ∨ hsame row B ∨ hsame row S ∨ hsame row WX ∨
              hsame row WY ∨ hsame row DX ∨ hsame row DY ∨ hsame row DZ ∨
                hsame row RX ∨ hsame row RY ∨ hsame row T ∨ hsame row H ∨
                  hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row leftRead ∨
                    hsame row rightRead ∨ hsame row tailRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont WX DX leftRead ∧ Cont WY DY rightRead ∧
              Cont DZ T tailRead ∧ PkgSig bundle tailRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro tailRead sourceTail
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
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeLeft, routeRight, routeTail, tailPkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary, tailUnary⟩

end BEDC.Derived.DyadicErrorBudgetUp
