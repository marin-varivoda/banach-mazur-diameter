import BMLean.Tables
import BMLean.Data.Hub058

namespace BMC

theorem hubOk_058 : hubChunkOk (parseRows BMD.hub058) = true := by native_decide

end BMC
