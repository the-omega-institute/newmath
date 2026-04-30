namespace BEDC.BaseReflection

structure BaseReflectionSetup where
  Hist : Type
  SigObj : Type
  Pkg : Type
  Pi : Type
  Domain : Type
  Evidence : Type
  hsame : SigObj → SigObj → Prop
  InDom : Domain → Hist → Prop
  SigGen : Pi → Hist → SigObj → Evidence → Prop
  TokIntro : Pi → SigObj → Pkg → Prop
  InGapSig : Pi → Domain → Pkg → Hist → Prop

structure HSameEquiv (s : BaseReflectionSetup) : Prop where
  refl  : ∀ x, s.hsame x x
  symm  : ∀ {x y}, s.hsame x y → s.hsame y x
  trans : ∀ {x y z}, s.hsame x y → s.hsame y z → s.hsame x z

end BEDC.BaseReflection
