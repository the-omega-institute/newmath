import BEDC.Derived.SequentialCompactUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SequentialCompactCarrier [AskSetup] [PackageSetup]
    (compact baire stream window regular realSeal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory compact ∧ UnaryHistory baire ∧ UnaryHistory stream ∧ UnaryHistory window ∧
    UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont compact baire stream ∧ Cont stream window regular ∧
          Cont regular realSeal transport ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg

theorem SequentialCompactCarrier_obligation_readiness [AskSetup] [PackageSetup]
    {compact baire stream window regular realSeal transport replay provenance localName
      sourceRead subsequenceRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier compact baire stream window regular realSeal transport replay
        provenance localName bundle pkg →
      Cont compact stream sourceRead →
        Cont sourceRead window subsequenceRead →
          Cont subsequenceRead regular regularRead →
            Cont regularRead realSeal sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory compact ∧ UnaryHistory baire ∧ UnaryHistory stream ∧
                  UnaryHistory window ∧ UnaryHistory regular ∧ UnaryHistory realSeal ∧
                    UnaryHistory sourceRead ∧ UnaryHistory subsequenceRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                        Cont compact stream sourceRead ∧
                          Cont sourceRead window subsequenceRead ∧
                            Cont subsequenceRead regular regularRead ∧
                              Cont regularRead realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sourceRoute subsequenceRoute regularRoute sealRoute sealPkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed carrier.left carrier.right.right.left sourceRoute
  have subsequenceUnary : UnaryHistory subsequenceRead :=
    unary_cont_closed sourceUnary carrier.right.right.right.left subsequenceRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed subsequenceUnary carrier.right.right.right.right.left regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary carrier.right.right.right.right.right.left sealRoute
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      sourceUnary,
      subsequenceUnary,
      regularReadUnary,
      sealUnary,
      sourceRoute,
      subsequenceRoute,
      regularRoute,
      sealRoute,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
      sealPkg⟩

end BEDC.Derived.SequentialCompactUp
