import BMLean.Tables
import BMLean.Data.Hub050

namespace BMC

theorem hubOk_050 : hubChunkOk (parseRows BMD.hub050) = true := by native_decide

end BMC
