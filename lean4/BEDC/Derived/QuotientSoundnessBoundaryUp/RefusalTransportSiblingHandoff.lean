import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundary_refusal_transport_sibling_handoff
    [AskSetup] [PackageSetup]
    {e a t v h c p n refusalRead consumer siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier e a t v h c p n bundle pkg →
      Cont v h refusalRead →
        Cont h c consumer →
          Cont consumer n siblingRead →
            PkgSig bundle siblingRead pkg →
              UnaryHistory e ∧ UnaryHistory a ∧ UnaryHistory t ∧ UnaryHistory v ∧
                UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory n ∧
                  UnaryHistory refusalRead ∧ UnaryHistory consumer ∧
                    UnaryHistory siblingRead ∧ Cont e a v ∧ Cont e t h ∧
                      Cont v h refusalRead ∧ Cont h c consumer ∧
                        Cont consumer n siblingRead ∧ hsame h n ∧
                          PkgSig bundle siblingRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier vHRefusal hCConsumer consumerNSibling siblingPkg
  obtain ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, _pUnary, nUnary, eAV,
    eTH, _hCN, _pPkg, _nPkg, hN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed vUnary hUnary vHRefusal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hUnary cUnary hCConsumer
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed consumerUnary nUnary consumerNSibling
  exact
    ⟨eUnary, aUnary, tUnary, vUnary, hUnary, cUnary, nUnary, refusalUnary,
      consumerUnary, siblingUnary, eAV, eTH, vHRefusal, hCConsumer,
      consumerNSibling, hN, siblingPkg⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
