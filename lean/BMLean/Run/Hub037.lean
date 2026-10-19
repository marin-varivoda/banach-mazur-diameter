import BMLean.Tables
import BMLean.Data.Hub037

namespace BMC

theorem hubOk_037 : hubChunkOk (parseRows BMD.hub037) = true := by native_decide

end BMC
