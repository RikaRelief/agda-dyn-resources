# Dynamical Resources

This is an Agda implementation of the formalization of resources we are using to think about resources when building RikaRelief or should we say RikaResource :stuck_out_tongue_closed_eyes:.

This particular formalization follows the theory given by this [paper](https://arxiv.org/abs/1409.5531). There the authors give a outline of resource
theories; basically a Symmetric Monoidal Category and what one can do with the resources in a particular resource theory. Everything one can say about
symmetric monoidal categories one can say about the resource theories presented in the paper.

For our purposes we also want to include the notion of Co-design as presented [here](https://arxiv.org/abs/1512.08055). This will help reason about what
resources can be used for; to give 'functionalities' we require. I.e what are the minimal resources required to give functionality X. It's obvious to see
how this relates to solving relief problems.

Additionally, there is a sense in which dynamical systems as described in the language of Polynomial Functors (a.k.a Poly) can be seen as resources. This
is what we are currently in the midst of fleshing out as it will give a more robust formalization of resources that can do more interesting things.
For more information on Polynomial Functors as a base for talking about interaction see this [book](https://topos.site/poly-book.pdf). Or even this
online [course](https://www.youtube.com/playlist?list=PLhgq-BqyZ7i6IjU82EDzCqgERKjjIPlmh)
