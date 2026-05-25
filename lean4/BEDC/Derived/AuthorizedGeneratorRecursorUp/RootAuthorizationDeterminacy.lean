import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_root_authorization_determinacy
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N route route' outputRead outputRead' boundaryRead
      boundaryRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont I E route →
        Cont I E route' →
          Cont O A outputRead →
            Cont O A outputRead' →
              Cont G N boundaryRead →
                Cont G N boundaryRead' →
                  PkgSig bundle outputRead pkg →
                    PkgSig bundle outputRead' pkg →
                      hsame route route' ∧ hsame outputRead outputRead' ∧
                        hsame boundaryRead boundaryRead' ∧ hsame H (append A C) ∧
                          PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  intro carrier rootRoute rootRoute' outputRoute outputRoute' boundaryRoute boundaryRoute'
    _outputPkg _outputPkg'
  obtain ⟨_IUnary, _EUnary, _MUnary, _BUnary, _DUnary, _OUnary, _AUnary, _HUnary,
    _CUnary, _PUnary, _GUnary, _NUnary, _signatureEliminatorMotive,
    _motiveBranchDescent, _descentOutputAudit, transportSame, provenancePkg⟩ := carrier
  have routeSame : hsame route route' :=
    cont_deterministic rootRoute rootRoute'
  have outputSame : hsame outputRead outputRead' :=
    cont_deterministic outputRoute outputRoute'
  have boundarySame : hsame boundaryRead boundaryRead' :=
    cont_deterministic boundaryRoute boundaryRoute'
  exact ⟨routeSame, outputSame, boundarySame, transportSame, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
