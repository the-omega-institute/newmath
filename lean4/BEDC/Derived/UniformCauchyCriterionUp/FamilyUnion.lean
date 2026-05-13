import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_paired_family_union_ledger [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name subA subB tailA
      tailB unionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows subA ->
        Cont index windows subB ->
          Cont subA tail tailA ->
            Cont subB tail tailB ->
              Cont tailA tailB unionRead ->
                PkgSig bundle tailA pkg ->
                  PkgSig bundle tailB pkg ->
                    PkgSig bundle unionRead pkg ->
                      UnaryHistory subA ∧ UnaryHistory subB ∧ UnaryHistory tailA ∧
                        UnaryHistory tailB ∧ UnaryHistory unionRead ∧ hsame subA subB ∧
                          hsame tailA tailB ∧ Cont index windows subA ∧
                            Cont index windows subB ∧ Cont subA tail tailA ∧
                              Cont subB tail tailB ∧ Cont tailA tailB unionRead ∧
                                PkgSig bundle name pkg ∧ PkgSig bundle tailA pkg ∧
                                  PkgSig bundle tailB pkg ∧ PkgSig bundle unionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsSubA indexWindowsSubB subATailA subBTailB tailUnion tailAPkg
    tailBPkg unionPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, _sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have subAUnary : UnaryHistory subA :=
    unary_cont_closed indexUnary windowsUnary indexWindowsSubA
  have subBUnary : UnaryHistory subB :=
    unary_cont_closed indexUnary windowsUnary indexWindowsSubB
  have tailAUnary : UnaryHistory tailA :=
    unary_cont_closed subAUnary tailUnary subATailA
  have tailBUnary : UnaryHistory tailB :=
    unary_cont_closed subBUnary tailUnary subBTailB
  have unionUnary : UnaryHistory unionRead :=
    unary_cont_closed tailAUnary tailBUnary tailUnion
  have sameSub : hsame subA subB :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsSubA
      indexWindowsSubB
  have sameTail : hsame tailA tailB :=
    cont_respects_hsame sameSub (hsame_refl tail) subATailA subBTailB
  exact
    ⟨subAUnary, subBUnary, tailAUnary, tailBUnary, unionUnary, sameSub, sameTail,
      indexWindowsSubA, indexWindowsSubB, subATailA, subBTailB, tailUnion, namePkg,
      tailAPkg, tailBPkg, unionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
