import BEDC.Derived.CauchyContinuousExtensionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyContinuousExtensionUp
namespace TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyContinuousExtensionCarrier_regular_tail_transport
    {S W D F U L H C P N regularTail sinkRead transported sourceRead toleranceRead
      extensionRead transportRead : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory F ->
            UnaryHistory H ->
              Cont S W regularTail ->
                Cont regularTail D sinkRead ->
                  Cont sinkRead H transported ->
                    Cont S W sourceRead ->
                      Cont sourceRead D toleranceRead ->
                        Cont toleranceRead F extensionRead ->
                          Cont H extensionRead transportRead ->
                            cauchyContinuousExtensionFields
                                (CauchyContinuousExtensionUp.mk S W D F U L H C P N) =
                              [S, W, D, F, U, L, H, C, P, N] ∧
                              UnaryHistory regularTail ∧ UnaryHistory sinkRead ∧
                                UnaryHistory transported ∧ Cont S W regularTail ∧
                                  Cont regularTail D sinkRead ∧ Cont sinkRead H transported ∧
                                    UnaryHistory sourceRead ∧ UnaryHistory toleranceRead ∧
                                      UnaryHistory extensionRead ∧
                                        UnaryHistory transportRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro sourceUnary windowUnary dyadicUnary mapUnary transportUnary sourceWindow tailDyadic
    sinkRoute sourceRoute toleranceRoute extensionRoute transportRoute
  have regularTailUnary : UnaryHistory regularTail :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have sinkReadUnary : UnaryHistory sinkRead :=
    unary_cont_closed regularTailUnary dyadicUnary tailDyadic
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed sinkReadUnary transportUnary sinkRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary windowUnary sourceRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed sourceReadUnary dyadicUnary toleranceRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed toleranceReadUnary mapUnary extensionRoute
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed transportUnary extensionReadUnary transportRoute
  exact
    ⟨rfl, regularTailUnary, sinkReadUnary, transportedUnary, sourceWindow, tailDyadic,
      sinkRoute, sourceReadUnary, toleranceReadUnary, extensionReadUnary, transportReadUnary⟩

end TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyContinuousExtensionCarrier [AskSetup] [PackageSetup]
    (S W D F U L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory F ∧
    UnaryHistory U ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyExtensionRegularTailTransport [AskSetup] [PackageSetup]
    {S W D F U L H C P N sinkRead transported named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousExtensionCarrier S W D F U L H C P N bundle pkg ->
      Cont S W sinkRead ->
        Cont sinkRead H transported ->
          Cont transported N named ->
            PkgSig bundle named pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row named ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row W ∨ hsame row D ∨ hsame row F ∨
                      hsame row U ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row named)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S W sinkRead ∧
                      Cont sinkRead H transported ∧ Cont transported N named ∧
                        PkgSig bundle named pkg)
                  hsame ∧ UnaryHistory sinkRead ∧ UnaryHistory transported ∧
                UnaryHistory named := by
  -- BEDC touchpoint anchor: CauchyContinuousExtensionCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sinkRoute transportRoute namedRoute namedPkg
  obtain ⟨unaryS, unaryW, _unaryD, _unaryF, _unaryU, _unaryL, unaryH, _unaryC,
    _unaryP, unaryN, _provenancePkg, _localNamePkg⟩ := carrier
  have sinkUnary : UnaryHistory sinkRead :=
    unary_cont_closed unaryS unaryW sinkRoute
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed sinkUnary unaryH transportRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed transportedUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row D ∨ hsame row F ∨
              hsame row U ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S W sinkRead ∧ Cont sinkRead H transported ∧
              Cont transported N named ∧ PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
      exact ⟨source.right, sinkRoute, transportRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, sinkUnary, transportedUnary, namedUnary⟩

end BEDC.Derived.CauchyContinuousExtensionUp
