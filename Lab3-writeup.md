# Lab 3 Write up

Hao Yuan

## Problem 1: Feed Back
 This lab helped with me understand the difference between static and dynamic scoping. 
 The auto grader should give better feed back than only showing a few test case. It is
 not helping when you pass all tests in the spec, you own case and references in auto grader 
 and yet the auto grader still given a bad grade. 

## Problem 2: 2(a)

    const x = 5;
    
    const f = function(m){
        return x
    }
    
    const g = function(n){
        const x = 20
        const y = n
        f(x-y)
    }
    
    f(1)
    g(2)
    
In static scope, the f(1) and g(2) will both return 5 since value of x in const f is bind with
the first line x = 5. So, no matter being called by what function, f will always return 5.
In dynamic scope, f(1) will return 5 since, in this case, value of x is bind with line 1 x = 5.
As for g, the the binding of x is at line 8, which is inside the definition of const g. So, x = 20.

## Problem 3: 3(d)

It is deterministic. The evaluation order is left associative.


## Problem 4: Evaluation order

The evaluation order is left associative, because e1 is always evaluated before e2. It can be changed
by altering the search rules to evaluate e2 before e1 and do rules to dive into the right side first. 

## Problem 5: 

a) The way we define "And" used short-circuit evaluation. For example, e1 && e2, Since evaluation order
is left associative, e1 will be evaluate first. If the result return for e1 is false, then there's no meaning
to calculate e2. Because no matter what value e2 have, the final result is false. 

b) Yes. The rule "DoAndFalse" return value of v1, which is false, without evaluate e2. 