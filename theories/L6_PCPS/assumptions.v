From CertiCoq Require Import L6.uncurry_proto L6.shrink_proto L6.inline_proto.

Goal True. idtac "---------- rw_uncurry assumptions ----------". Abort.
Print Assumptions rw_uncurry.
Goal True. idtac "---------- rw_inline assumptions ----------". Abort.
Print Assumptions rw_inline.
Goal True. idtac "---------- rw_shrink assumptions ----------". Abort.
Print Assumptions rw_shrink.
