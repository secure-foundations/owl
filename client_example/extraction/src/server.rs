pub use vstd::{modes::*, prelude::*, seq::*, view::*};
pub use crate::*;

// Everything in this file is handwritten

verus! {

// hack since we can't use `x - 1` inside itree syntax
pub open spec fn decrement(x: usize) -> usize {
    (x - 1) as usize
}

pub open spec fn echo_server_main_spec(cfg: cfg_Server, mut_state: state_Server, fuel: usize) -> ITree<((), state_Server), Endpoint> 
    decreases fuel
{
    if fuel == 0 {
        owl_spec!(mut_state, state_Server, (ret(())))
    } else {
        owl_spec!(mut_state, state_Server,
            let recv_result = (call(server_recv_spec(cfg, mut_state))) in
            (case (recv_result) {
                | owlSpec_ServerResult::owlSpec_SROk(ptxt) => {
                    let _ = (call(server_send_spec(cfg, mut_state, ptxt))) in
                    (call(echo_server_main_spec(cfg, mut_state, decrement(fuel))))
                },
                | owlSpec_ServerResult::owlSpec_SRErr() => {
                    (call(echo_server_main_spec(cfg, mut_state, decrement(fuel))))
                },
            })
        )
    }
}

impl cfg_Server<'_> {

    pub fn echo_server_main_loop(
        &self,
        Tracked(itree): Tracked<ITreeToken<((), state_Server), Endpoint>>,
        mut_state: &mut state_Server,
        fuel: usize,
    ) -> (res: Result<((), Tracked<ITreeToken<((), state_Server), Endpoint>>), OwlError>)
        requires
            itree.view() == echo_server_main_spec(*self, *old(mut_state), fuel),
        ensures
            res matches Ok(r) ==> (r.1).view().view().results_in(((), *mut_state)),
    {
        let (res_inner, Tracked(itree)): ((), Tracked<ITreeToken<((), state_Server), Endpoint>>) = {
            broadcast use itree_axioms;

            // beginning of actual implementation code

            let mut fuel = fuel;
            let tracked mut itree = itree;

            while (fuel > 0) 
                invariant 
                    itree.view() == echo_server_main_spec(*self, *mut_state, fuel),
                decreases fuel
            {
                let (recv_result, Tracked(itree1)) = owl_call!(itree, *mut_state, server_recv_spec(*self, *mut_state), self.owl_server_recv(mut_state));
                proof { itree = itree1; }
                let Tracked(itree1) = match recv_result {
                    owl_ServerResult::owl_SROk(ptxt) => {
                        let (_, Tracked(itree1)) = owl_call!(itree, *mut_state, server_send_spec(*self, *mut_state, ptxt@), self.owl_server_send(mut_state, ptxt));
                        proof { itree = itree1; }
                        
                        proof { 
                            let tracked (Tracked(next_itree), Tracked(cont_itree)) = split_bind(itree, echo_server_main_spec(*self, *mut_state, decrement(fuel)));
                            itree = next_itree;
                        }
                        Tracked(itree)
                    },
                    owl_ServerResult::owl_SRErr() => {
                        proof { 
                            let tracked (Tracked(next_itree), Tracked(cont_itree)) = split_bind(itree, echo_server_main_spec(*self, *mut_state, decrement(fuel)));
                            itree = next_itree;
                        }
                        Tracked(itree)
                    }, 
                };
                proof { itree = itree1; }
                fuel = fuel - 1;
            }

            ((), Tracked(itree))
        };
        Ok((res_inner, Tracked(itree)))
    }
        
}

} // verus!