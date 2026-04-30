import BEDC.FKernel.Mark

namespace BEDC.Derived.BoolUp

def BoolCarrier : Type := BEDC.FKernel.Mark.BMark

def BoolSourceSpec (value : BEDC.FKernel.Mark.BMark) : Prop :=
  BEDC.FKernel.Mark.msame value BEDC.FKernel.Mark.BMark.b0 ∨
    BEDC.FKernel.Mark.msame value BEDC.FKernel.Mark.BMark.b1

end BEDC.Derived.BoolUp
