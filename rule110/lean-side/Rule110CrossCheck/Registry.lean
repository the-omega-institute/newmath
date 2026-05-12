
namespace BEDC.Rule110CrossCheck

def targetMsameRefl : String := "BEDC.FKernel.Mark.msame_refl"
def targetMsameSymm : String := "BEDC.FKernel.Mark.msame_symm"
def targetMsameTrans : String := "BEDC.FKernel.Mark.msame_trans"
def targetMsameNoConfusion : String := "BEDC.FKernel.Mark.msame_no_confusion"
def targetHsameRefl : String := "BEDC.FKernel.Hist.hsame_refl"
def targetHsameSymm : String := "BEDC.FKernel.Hist.hsame_symm"
def targetHsameTrans : String := "BEDC.FKernel.Hist.hsame_trans"
def targetHsameEmpty : String := "BEDC.FKernel.Hist.hsame_empty_inversion/BEDC.FKernel.Hist.hsame_empty_iff"
def targetHsameDistinct : String := "BEDC.FKernel.Hist.hsame_no_confusion"
def targetExtStep : String := "BEDC.FKernel.Ext.Ext.e0/BEDC.FKernel.Ext.Ext.e1"
def targetCont : String := "BEDC.FKernel.Cont.Cont"
def targetSigRel : String := "BEDC.FKernel.Sig.SigRel"
def targetSameSig : String := "BEDC.FKernel.Sig.SameSig"
def targetBundleLength : String := "BEDC.FKernel.Bundle length/append theorem family"
def targetBundleMembership : String := "BEDC.FKernel.Bundle membership/append theorem family"
def targetUnary : String := "BEDC.FKernel.Unary.UnaryHistory/UnaryCont"
def targetAsk : String := "BEDC.FKernel.Ask.Ask"
def targetExternalBinary : String := "BEDC.FKernel.ExternalBinary.append"
def targetGap : String := "BEDC.FKernel.Gap.InGapSig/CompGap fixture"
def targetPackage : String := "BEDC.FKernel.Package.TokIntro/psame"
def targetNameCert : String := "BEDC.FKernel.NameCert fixture"
def targetSettled : String := "BEDC.FKernel.Settled.SettledKernelCriterion projections"

inductive Family where
  | markRefl
  | markSymm
  | markTrans
  | markNoConfusion
  | histRefl
  | histSymm
  | histTrans
  | histEmpty
  | histDistinct
  | ext
  | cont
  | sigRel
  | sameSig
  | bundleLength
  | bundleMembership
  | unary
  | ask
  | externalBinary
  | gap
  | package
  | nameCert
  | settled
  deriving Repr, DecidableEq

def Family.name : Family -> String
  | .markRefl => "mark/msame_refl"
  | .markSymm => "mark/msame_symm"
  | .markTrans => "mark/msame_trans"
  | .markNoConfusion => "mark/msame_no_confusion"
  | .histRefl => "hist/hsame_refl"
  | .histSymm => "hist/hsame_symm"
  | .histTrans => "hist/hsame_trans"
  | .histEmpty => "hist/hsame_empty_inversion"
  | .histDistinct => "hist/hsame_constructor_distinct"
  | .ext => "ext/ext_step"
  | .cont => "cont/cont_basic"
  | .sigRel => "sig/sigrel_basic"
  | .sameSig => "sig/samesig_equiv"
  | .bundleLength => "bundle/bundle_length"
  | .bundleMembership => "bundle/bundle_membership"
  | .unary => "unary/unary_basic"
  | .ask => "ask/ask_basic"
  | .externalBinary => "external_binary/external_binary_basic"
  | .gap => "gap/gap_basic"
  | .package => "package/package_basic"
  | .nameCert => "name_cert/name_cert_basic"
  | .settled => "settled/settled_basic"

def Family.targetKey : Family -> String
  | .markRefl => targetMsameRefl
  | .markSymm => targetMsameSymm
  | .markTrans => targetMsameTrans
  | .markNoConfusion => targetMsameNoConfusion
  | .histRefl => targetHsameRefl
  | .histSymm => targetHsameSymm
  | .histTrans => targetHsameTrans
  | .histEmpty => targetHsameEmpty
  | .histDistinct => targetHsameDistinct
  | .ext => targetExtStep
  | .cont => targetCont
  | .sigRel => targetSigRel
  | .sameSig => targetSameSig
  | .bundleLength => targetBundleLength
  | .bundleMembership => targetBundleMembership
  | .unary => targetUnary
  | .ask => targetAsk
  | .externalBinary => targetExternalBinary
  | .gap => targetGap
  | .package => targetPackage
  | .nameCert => targetNameCert
  | .settled => targetSettled

def registeredManifestSpecs : List (String × Family) := [
  ("manifests/mark/msame_refl.enum.ct", .markRefl),
  ("manifests/mark/msame_symm.enum.ct", .markSymm),
  ("manifests/mark/msame_trans.enum.ct", .markTrans),
  ("manifests/mark/msame_no_confusion.enum.ct", .markNoConfusion),
  ("manifests/hist/hsame_refl.enum.ct", .histRefl),
  ("manifests/hist/hsame_symm.enum.ct", .histSymm),
  ("manifests/hist/hsame_trans.enum.ct", .histTrans),
  ("manifests/hist/hsame_empty_inversion.enum.ct", .histEmpty),
  ("manifests/hist/hsame_constructor_distinct.enum.ct", .histDistinct),
  ("manifests/ext/ext_step.enum.ct", .ext),
  ("manifests/cont/cont_basic.enum.ct", .cont),
  ("manifests/sig/sigrel_basic.enum.ct", .sigRel),
  ("manifests/sig/samesig_equiv.enum.ct", .sameSig),
  ("manifests/bundle/bundle_length.enum.ct", .bundleLength),
  ("manifests/bundle/bundle_membership.enum.ct", .bundleMembership),
  ("manifests/unary/unary_basic.enum.ct", .unary),
  ("manifests/ask/ask_basic.enum.ct", .ask),
  ("manifests/external_binary/external_binary_basic.enum.ct", .externalBinary),
  ("manifests/gap/gap_basic.enum.ct", .gap),
  ("manifests/package/package_basic.enum.ct", .package),
  ("manifests/name_cert/name_cert_basic.enum.ct", .nameCert),
  ("manifests/settled/settled_basic.enum.ct", .settled)
]

def familyOfPath (path : String) : Except String Family := do
  match registeredManifestSpecs.find? (fun spec => path.endsWith spec.fst) with
  | some spec => pure spec.snd
  | none => throw s!"unsupported manifest path: {path}"

end BEDC.Rule110CrossCheck
