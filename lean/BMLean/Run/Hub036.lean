import BMLean.Tables
import BMLean.Data.Hub036

namespace BMC

theorem hubOk_036 : hubChunkOk (parseRows BMD.hub036) = true := by native_decide

end BMC
