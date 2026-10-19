import BMLean.Tables
import BMLean.Data.Hub033

namespace BMC

theorem hubOk_033 : hubChunkOk (parseRows BMD.hub033) = true := by native_decide

end BMC
