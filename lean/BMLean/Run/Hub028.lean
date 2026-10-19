import BMLean.Tables
import BMLean.Data.Hub028

namespace BMC

theorem hubOk_028 : hubChunkOk (parseRows BMD.hub028) = true := by native_decide

end BMC
