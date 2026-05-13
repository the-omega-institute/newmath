import Rule110CrossCheck.Families.Cont

namespace BEDC.Rule110CrossCheck

def checkExternalBinary (path : String) (a : Assertion) : Except String String :=
  checkContLike .externalBinary "external_append_holds" path a

end BEDC.Rule110CrossCheck
