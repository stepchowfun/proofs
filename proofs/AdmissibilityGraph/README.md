# Admissibility graphs

Most programming languages have some support for [encapsulation](https://en.wikipedia.org/wiki/Encapsulation_\(computer_programming\)), such as [access modifiers](https://en.wikipedia.org/wiki/Access_modifiers) (`public`, `private`, etc.), [module systems](https://jozefg.bitbucket.io/posts/2015-01-08-modules.html), [existential types](https://groups.seas.harvard.edu/courses/cs152/2014sp/lectures/lec17-existential.pdf), and [closures](https://en.wikipedia.org/wiki/Closure_\(computer_programming\)). Encapsulation is a versatile concept in system design and isn't limited to just programming language features. For example, in a microservices architecture, it's common for a service to have its own database, with all access to that data being mediated by the service for the purposes of maintaining invariants and presenting a clear interface to downstream dependencies. In this tutorial, I'll introduce a general mathematical theory called *admissibility graphs* which can be used to model encapsulation in many different situations. I hope you find it interesting!

<p align="center"><img width="608" src="Images/graph-10.svg"></p>
<p align="center"><em>An example admissibility graph.</em></p>

Time will tell how useful this concept ends up being, but I believe it sheds new light on the relationship between *dependencies* and *implementation details* and enables us to reason about these notions in a rigorous way. It proposes principled answers to abstract questions such as:

- How are the notions of dependencies and implementation details related?
- When should a dependency be allowed?
- Are things implementation details of themselves?
- Does the existence of circular dependencies imply that two distinct things are implementation details of each other?

These questions may seem philosophical, but the answers have practical consequences for any system which allows its users to define abstractions. Such systems include programming languages, network infrastructure, build systems, etc.

## Definition

Before we look at any particular examples, allow me to first define the general concept.

### Nodes and child-parent relationships

An admissibility graph, like any [graph](https://en.wikipedia.org/wiki/Graph_\(discrete_mathematics\)), has a set of **nodes**. The nodes might represent entities such as functions in a program or microservices in a distributed system.

The edges of an admissibility graph are called **child-parent relationships**. These relationships specify which nodes are considered to be encapsulated within other nodes; *children* are implementation details of their *parents*. A node can have multiple children and multiple parents. A child-parent relationship is depicted as a solid arrow from a child to a parent.

<p align="center"><img width="234" src="Images/child-parent-relationship.svg"></p>
<p align="center"><em>A child-parent relationship.</em></p>

### The reflexivity axiom

Admissibility graphs are required to satisfy the following mathematical law:

> **(Reflexivity)** Every node is a parent of itself.

The motivation for this axiom will be explained below.

### Dependencies and admissibility

For our purposes, *dependencies* are arbitrary connections between nodes. For example, dependencies might indicate functions calling other functions or microservices making [RPCs](https://en.wikipedia.org/wiki/Remote_procedure_call) to other microservices. A node can depend on multiple *target* nodes and can be depended on by multiple *source* nodes. A dependency is depicted as a dotted arrow from a source to a target.

  <p align="center"><img width="234" src="Images/dependency.svg"></p>
  <p align="center"><em>A dependency.</em></p>

A technical note: we don't consider dependencies to part of the admissibility graph. Rather, they are the edges of a related graph with the same nodes called a *dependency graph*. The admissibility graph is a specification for which dependencies are allowed in the dependency graph.

Define *ancestry* as the [transitive closure](https://en.wikipedia.org/wiki/Transitive_closure) of the child-parent relation. That means `A` is an *ancestor* of `D` (`D` is a *descendant* of `A`) when there is a path from `D` to `A` via child-parent relationships.

A target node `T` *admits* a source node `S` (`S` is *admitted by* `T`) when there is an ancestor `A` of `S` and a descendant `D` of `T` such that `A` is a parent of `D`. In other words, `T` *admits* `S` when there is a path from `S` to `T` via child-parent relationships in which one of the relationships is flipped. A dependency is *admissible* when the target admits the source. Admissibility might seem mysterious at first, but we'll come to understand it through examples.

## Examples

To explore the consequences of the definitions and build intuition for them, let's look at some examples.

### Admissibility basics

Let's start with the following admissibility graph.

<p align="center"><img width="153" src="Images/graph-00.svg"></p>

First, we can check that the reflexivity axiom is satisfied. Reflexivity says every node is a parent (and child) of itself. This can be interpreted as saying that every node is part of its own implementation. That may seem like a philosophical position, but we'll see [later](#special-cases-of-admissibility) that it has important practical consequences.

Now let's consider admissibility. In this example, `B` and `C` are considered implementation details of `A`, and `D` is an implementation detail of `C`. What dependencies does this admissibility graph allow?

#### Nodes can depend on their children

Intuitively, a node should be able to depend on its implementation details. So, for every child-parent relationship, we can have a dependency on the child by the parent.

<p align="center"><img width="153" src="Images/graph-01.svg"></p>

You're encouraged to check that these dependencies are admissible according to the definition.

#### Siblings can depend on each other

Since `B` and `C` are both part of the implementation of `A`, they can depend on each other.

<p align="center"><img width="153" src="Images/graph-02.svg"></p>

So, in the absence of additional stipulations, admissibility graphs allow for circular dependencies, even though ancestry cycles are forbidden.

#### Nodes can depend on any nodes their parents can depend on

Since `C` is allowed to depend on `B`, the implementation of `C` should be allowed to depend on `B` as well. So `D` can depend on `B`.

<p align="center"><img width="153" src="Images/graph-03.svg"></p>

#### Nodes can't depend on their grandchildren or [niblings](https://www.merriam-webster.com/words-at-play/words-were-watching-nibling) in general

`A` can't depend on `D`, since `D` is an implementation detail of `C`.

<p align="center"><img width="153" src="Images/graph-04.svg"></p>

For the same reason, `B` can't depend on `D`.

<p align="center"><img width="153" src="Images/graph-05.svg"></p>

### Modularity

We'd like to be able to group nodes together and manage them as a single unit from an admissibility perspective. For example, we might wish to allow a group of nodes to depend on another group of nodes, but not vice versa, and without quadratically many child-parent relationships. Is that possible?

#### A first attempt

We could try to group nodes together by arranging them in an ancestry cycle:

<p align="center"><img width="153" src="Images/graph-06.svg"></p>

This approach has a major flaw. Suppose `C` has implementation detail `D`. The problem is that other nodes in the cycle such as `B` can depend on `D`, which doesn't match our expectation that `D` is encapsulated within `C`.

<p align="center"><img width="153" src="Images/graph-07.svg"></p>

But then what should we do instead?

#### A proper module

We can arrange the nodes into a *module* by introducing gateway nodes to manage ingress and egress.

<p align="center"><img width="256" src="Images/graph-08.svg"></p>

Then the egress gateway can be *bridged* with upstream nodes by giving them a common parent, and likewise the ingress gateway can be bridged with downstream nodes.

<p align="center"><img width="468" src="Images/graph-09.svg"></p>

In this example, the upstream node `X` is a sibling of the egress gateway, so members of the module (e.g., `A`) can depend on it. The downstream node `Y` is a sibling of the ingress gateway, so it can depend on members of the module (e.g., `C`).

It's natural to wonder whether a single node could serve as both the ingress and egress gateways for the same module. That would create an ancestry cycle containing all the nodes of the module, which would enable each node of the module to access the implementation details of every other node of the module. A better strategy is to bridge an external node with both the ingress and egress gateways of a module when both directions are needed for that external node.

#### Bridging modules

To allow the contents of one module to depend on the contents of another, we can bridge the egress gateway of the former and the ingress gateway of the latter:

<p align="center"><img width="608" src="Images/graph-10.svg"></p>

In this example, the contents of module `M` can depend on the contents of module `N` (as demonstrated by the dependency on `X` by `C`), but not vice versa. Mutual admissibility can be arranged by also bridging the ingress of `M` and the egress of `N`, possibly using the same bridge as before. In general, arbitrary admissibility relationships between modules can be configured by bridging gateways.

#### Modular encapsulation

Suppose we want to make node `Y` a private implementation detail of module `N`, such that members of the other modules like `M` can't depend on it. We can simply disconnect `Y` from the ingress gateway of `N`.

<p align="center"><img width="256" src="Images/graph-11.svg"></p>

## Special cases of admissibility

A dependency is admissible when the target is an ancestor of a child of an ancestor of the source. In this section, we consider two common special cases of that criterion.

### Ancestors of children

A consequence of the definition of admissibility is that *a node is admitted by any ancestors of its children*. From this, we can draw many conclusions:

- A node is admitted by its own children.
- A node is admitted by parents of its children, including itself.
- A node is admitted by grandparents of its children, including its own parents.
- …
- A node is admitted by its own ancestors.

The second conclusion would seem to imply that admissibility is reflexive, which might make one wonder why the reflexivity axiom is needed. The complication is that this conclusion only applies when the node has children. The reflexivity axiom says it doesn't matter—every node has at least one child (itself).

### Children of ancestors

Another consequence of the definition of admissibility is that *a node is admitted by any children of its ancestors*. From this, we can also draw many conclusions, including some we've already seen:

- A node is admitted by its own children.
- A node is admitted by children of its parents, including itself.
- A node is admitted by children of its grandparents, including its own parents.
- …
- A node is admitted by its own ancestors.

As before, the second conclusion seems to imply that admissibility is reflexive, but that only follows when the node has parents. The reflexivity axiom says it doesn't matter—every node has at least one parent (itself).

## Deciding admissibility

Given an admissibility graph, let *N* be the number of nodes. Then the graph can be checked for validity against the reflexivity axiom in 𝒪(*N*) time and 𝒪(1) space by verifying each node individually.

More interestingly, we may wish to check whether a dependency graph is compatible with a given admissibility graph containing the same nodes. Let *E* be the number of child-parent relationships, and let *D* be the number of dependencies. Then we can validate the dependency graph in 𝒪(*N*² + *NE*) expected time and 𝒪(*N* + *D*) space in the worst case by defining an auxiliary graph as follows:

- For every node `X` in the admissibility graph, the auxiliary graph will have two nodes `X₁` and `X₂`.
- For every child-parent relationship `C` → `P`, the auxiliary graph will have edges `C₁` → `P₁`, `C₂` → `P₂`, and `P₁` → `C₂`.

Then, to check that a dependency `S` → `T` is admissible, it suffices to check that `T₂` is reachable from `S₁` in the auxiliary graph. This can be done with DFS in 𝒪(*N* + *E*) time and 𝒪(*N*) space. If we traverse all the nodes `T₂` reachable from some source `S₁` (e.g., with a depth-first strategy), we discover all the nodes which admit that source, again in 𝒪(*N* + *E*) time and 𝒪(*N*) space. By doing this for every source `S₁`, we can discover all the admissible dependencies in the admissibility graph. Any dependencies which weren't discovered (which can be recorded by a hash table) aren't admissible.
