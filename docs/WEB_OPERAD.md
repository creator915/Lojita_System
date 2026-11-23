# Canvas scenes and observations

`LojitaCtx.WebOperad.Scene A` describes a scene with typed owners and geometry. The pure library computes drawing commands, hit-tests rational points and projects frame state. A node can use these operations to state a law about hit routing or a rendered scene in a simulated world. [Scene operations](../LojitaCtx/WebOperad.lean)

A session probe can open `webSlot` at an explicit viewport size, flush draw commands, inspect pixels, resize and export a PPM to an owned file. The native relay returns acknowledgements, frame counts and digests, or RGB observations. The worker restores the owned files when the service stops. [Web tool](../Lojita/Ownership/Tools/Web.lean) · [Canvas relay](../runtime/tools/web-relay.c) · [Checked example](../Test/S4/relay-probe.lean)
