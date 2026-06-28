import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalEndpointEnclosureTransport [AskSetup] [PackageSetup]
    {L U E D W R S H C N L' U' E' D' W' R' transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L -> UnaryHistory U -> UnaryHistory E -> UnaryHistory D ->
      UnaryHistory W -> UnaryHistory H -> UnaryHistory N -> hsame L L' -> hsame U U' ->
        hsame E E' -> hsame D D' -> hsame W W' -> hsame R R' -> Cont L U E ->
          Cont D W R -> Cont R E S -> Cont S H C -> Cont C N transportedRead ->
            PkgSig bundle N pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row L' ∨ hsame row U' ∨ hsame row E' ∨ hsame row D' ∨
                      hsame row W' ∨ hsame row R' ∨ hsame row S ∨ hsame row H ∨
                        hsame row C ∨ hsame row N ∨ hsame row transportedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont L U E ∧ Cont D W R ∧ Cont R E S ∧
                      Cont S H C ∧ Cont C N transportedRead ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory C ∧
                  UnaryHistory transportedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro _unaryL _unaryU unaryE unaryD unaryW unaryH unaryN _sameL _sameU _sameE
    _sameD _sameW sameR _endpointRoute dyadicRoute enclosureRoute replayRoute
    transportedRoute pkgN
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryD unaryW dyadicRoute
  have _unaryR' : UnaryHistory R' :=
    unary_transport unaryR sameR
  have unaryS : UnaryHistory S :=
    unary_cont_closed unaryR unaryE enclosureRoute
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryS unaryH replayRoute
  have unaryTransported : UnaryHistory transportedRead :=
    unary_cont_closed unaryC unaryN transportedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L' ∨ hsame row U' ∨ hsame row E' ∨ hsame row D' ∨
              hsame row W' ∨ hsame row R' ∨ hsame row S ∨ hsame row H ∨
                hsame row C ∨ hsame row N ∨ hsame row transportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U E ∧ Cont D W R ∧ Cont R E S ∧
              Cont S H C ∧ Cont C N transportedRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro transportedRead
        ⟨hsame_refl transportedRead, unaryTransported⟩
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
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, _endpointRoute, dyadicRoute, enclosureRoute, replayRoute,
          transportedRoute, pkgN⟩
  }
  exact ⟨cert, unaryR, unaryS, unaryC, unaryTransported⟩

end BEDC.Derived.RealIntervalUp
