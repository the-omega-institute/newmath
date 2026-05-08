import BEDC.Derived.RealUp.SemanticCertificate

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

theorem RealUp_concrete_to_schema :
    SemanticNameCert RealConstantHistoryCarrier RealConstantHistoryCarrier
        RealConstantHistoryCarrier RealConstantHistoryClassifier ∧
      (forall {d : BHist},
        RatHistoryCarrier d -> RealConstantHistoryCarrier (BHist.e1 d)) ∧
        (forall {d e : BHist},
          RatHistoryClassifier d e ->
            RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e)) := by
  have bridge := RealConstant_rational_embedding_certificate
  constructor
  · exact bridge.left
  · constructor
    · intro d ratCarrier
      have streamCarrier :
          BEDC.Derived.StreamNameUp.RatStreamNameCarrier
            (BEDC.Derived.StreamNameUp.RatConstStream d) :=
        Iff.mp (bridge.right.left (d := d)).left ratCarrier
      exact Iff.mp (bridge.right.left (d := d)).right streamCarrier
    · intro d e ratClassifier
      have streamClassifier :
          BEDC.Derived.StreamNameUp.RatStreamNameClassifier
            (BEDC.Derived.StreamNameUp.RatConstStream d)
            (BEDC.Derived.StreamNameUp.RatConstStream e) :=
        Iff.mp (bridge.right.right (d := d) (e := e)).left ratClassifier
      have unaryClassifier :
          RealUnaryStreamClassifier
            (BEDC.Derived.StreamNameUp.RatConstStream d)
            (BEDC.Derived.StreamNameUp.RatConstStream e) :=
        Iff.mp (bridge.right.right (d := d) (e := e)).right.left streamClassifier
      exact Iff.mp (bridge.right.right (d := d) (e := e)).right.right unaryClassifier

end BEDC.Derived.RealUp
