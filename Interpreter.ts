///<reference path="World.ts"/>
///<reference path="Parser.ts"/>
/**
* Interpreter module
* 
* The goal of the Interpreter module is to interpret a sentence
* written by the user in the context of the current world state. In
* particular, it must figure out which objects in the world,
* i.e. which elements in the `objects` field of WorldState, correspond
* to the ones referred to in the sentence. 
*
* Moreover, it has to derive what the intended goal state is and
* return it as a logical formula described in terms of literals, where
* each literal represents a relation among objects that should
* hold. For example, assuming a world state where "a" is a ball and
* "b" is a table, the command "put the ball on the table" can be
* interpreted as the literal ontop(a,b). More complex goals can be
* written using conjunctions and disjunctions of these literals.
*
* In general, the module can take a list of possible parses and return
* a list of possible interpretations, but the code to handle this has
* already been written for you. The only part you need to implement is
* the core interpretation function, namely `interpretCommand`, which produces a
* single interpretation for a single command.
*/
module Interpreter {

    //////////////////////////////////////////////////////////////////////
    // exported functions, classes and interfaces/types

/**
Top-level function for the Interpreter. It calls `interpretCommand` for each possible parse of the command. No need to change this one.
* @param parses List of parses produced by the Parser.
* @param currentState The current state of the world.
* @returns Augments ParseResult with a list of interpretations. Each interpretation is represented by a list of Literals.
*/    
    export function interpret(parses : Parser.ParseResult[], currentState : WorldState) : InterpretationResult[] {
        var errors : Error[] = [];
        var interpretations : InterpretationResult[] = [];
        parses.forEach((parseresult) => {
            try {
                var result : InterpretationResult = <InterpretationResult>parseresult;
                result.interpretation = interpretCommand(result.parse, currentState);
                interpretations.push(result);
            } catch(err) {
                errors.push(err);
            }
        });
        if (interpretations.length) {
            return interpretations;
        } else {
            // only throw the first error found
            throw errors[0];
        }
    }

    export interface InterpretationResult extends Parser.ParseResult {
        interpretation : DNFFormula;
    }

    export type DNFFormula = Conjunction[];
    type Conjunction = Literal[];

    /**
    * A Literal represents a relation that is intended to
    * hold among some objects.
    */
    export interface Literal {
	/** Whether this literal asserts the relation should hold
	 * (true polarity) or not (false polarity). For example, we
	 * can specify that "a" should *not* be on top of "b" by the
	 * literal {polarity: false, relation: "ontop", args:
	 * ["a","b"]}.
	 */
        polarity : boolean;
	/** The name of the relation in question. */
        relation : string;
	/** The arguments to the relation. Usually these will be either objects 
     * or special strings such as "floor" or "floor-N" (where N is a column) */
        args : string[];
    }

    export function stringify(result : InterpretationResult) : string {
        return result.interpretation.map((literals) => {
            return literals.map((lit) => stringifyLiteral(lit)).join(" & ");
            // return literals.map(stringifyLiteral).join(" & ");
        }).join(" | ");
    }

    export function stringifyLiteral(lit : Literal) : string {
        return (lit.polarity ? "" : "-") + lit.relation + "(" + lit.args.join(",") + ")";
    }

    //////////////////////////////////////////////////////////////////////
    // private functions
    /**
     * The core interpretation function. The code here is just a
     * template; you should rewrite this function entirely. In this
     * template, the code produces a dummy interpretation which is not
     * connected to `cmd`, but your version of the function should
     * analyse cmd in order to figure out what interpretation to
     * return.
     * @param cmd The actual command. Note that it is *not* a string, but rather an object of type `Command` (as it has been parsed by the parser).
     * @param state The current state of the world. Useful to look up objects in the world.
     * @returns A list of list of Literal, representing a formula in disjunctive normal form (disjunction of conjunctions). See the dummy interpetation returned in the code for an example, which means ontop(a,floor) AND holding(b).
     */
    function interpretCommand(cmd : Parser.Command, state : WorldState) : DNFFormula {
         // 3 commands : take, move, drop 
        var interpretation: DNFFormula = [];
        if (cmd.command == "take") {
            var e: Parser.Entity = cmd.entity;
            var is1: string[][] = findIdents(e.object, state);
            while (e.object.location != null) {
                var is2: string[][] = findIdents(e.object.location.entity.object, state);
                is1 = findRelatedIdents(is1, is2, e.object.location.relation, state);
                e = e.object.location.entity;
            }
            for (var i = 0; i < is1.length; i++) {
                interpretation.push([{ polarity: true, relation: "holding", args: [is1[i][0]] }]);
            }
        } else if (cmd.command == "move") {
            var e1: Parser.Entity = cmd.entity;
            var l: Parser.Location = cmd.location; 
            var e2: Parser.Entity = cmd.location.entity;
            var idents1: string[][] = findIdents(e1.object, state);
            var idents2: string[][] = findIdents(e2.object, state);
            while (e1.object.location != null) {
                var s: string[][] = findIdents(e1.object.location.entity.object, state);
                idents1 = findRelatedIdents(idents1, s, e1.object.location.relation, state);
                e1 = e1.object.location.entity;
            }            
            while (e2.object.location != null) {
                var s: string[][] = findIdents(e2.object.location.entity.object, state);
                idents2  = findRelatedIdents(idents2, s, e2.object.location.relation, state);
                e2 = e2.object.location.entity;
            }
            for (var i = 0; i < idents1.length; i++) {
                for (var j = 0; j < idents2.length; j++) {
                    if (idents1[i][0] != idents2[j][0]) {
                        if (l.relation == "inside" || l.relation == "ontop") {
                            if (isOkSupport(idents1[i][0], idents2[j][0], state)) {
                                interpretation.push([{ polarity: true, relation: l.relation, args: [idents1[i][0], idents2[j][0]] }]);
                            }
                        } else {
                            interpretation.push([{ polarity: true, relation: l.relation, args: [idents1[i][0], idents2[j][0]] }]);
                        }
                    }
                }
            } 
        } 
        else if (cmd.command=="drop")
            //I hope this means "not holding anything"
            interpretation.push([{polarity:true, relation:"holding", args:[]}]);

        if (interpretation.length == 0) {
            interpretation = null;
        } 
        console.log(interpretation[0]);
        return interpretation;
    }

    function findPosition (ident: string, state: WorldState): number[]{
        var pos: number[] = []
        var stacks: Stack[] = state.stacks;
        var col: number = 0;
        var row: number = 0;
        for (var i = 0; i < stacks.length; i++) {
            for (var j = 0; j < stacks[i].length; j++) {
                if (stacks[i][j]== ident) {
                    col = i;
                    row = j;
                }
            }
        }
       return [col,row]; 
    }

    /* find identifiers that satisfy the object description */
    function findIdents(o: Parser.Object, state: WorldState): string[][] {
        var obj: Parser.Object = o;
        if (o.object != null) {
            obj = o.object;
        }
        var objects: string[] = Array.prototype.concat.apply([], state.stacks);
        var n: number = objects.length;
        var idents: string[][] = [];
        if (obj.form == "floor") {
            idents.push(["floor"]);
        } else {
            for (var i = 0; i < n; i++) {
                if (objectMatch(obj, state.objects[objects[i]])) {
                    idents.push([objects[i]]);
                }
            }      
        }
        return idents;
    }
 
    function objectMatch(o1: Parser.Object, o2: Parser.Object): boolean {
        return ((o1.color == null || o1.color == o2.color)
            && (o1.size == null || o1.size == o2.size)
            && (o1.form == "anyform" || o1.form == o2.form));// if o2.form == floor ? 
    }

    /* checks if object1 can be supported by object2 */
    function isOkSupport(ident1 :string, ident2: string, state: WorldState): boolean {
        if (ident2 == "floor") {
            return true;
        } else {
            var o1: Parser.Object = state.objects[ident1];
            var o2: Parser.Object = state.objects[ident2];
            //Balls must be in boxes or on the floor, otherwise they roll away.
            if (o1.form == "ball" && o2.form != "box" && o2.form != "floor") { // floor ??
                return false;
            } else if (o2.form == "ball") { //Balls cannot support anything.
                return false;
                //Small objects cannot support large objects
            } else if (o1.size == "large" && o2.size == "small") {
                return false;
                //Boxes cannot contain pyramids, planks or boxes of the same size.  
            } else if (o2.form == "box" && o2.size == o1.size && (o1.form == "pyramid" || o1.form == "plank" ||  o1.form == "box")) {
                return false;
                //Small boxes cannot be supported by small bricks or pyramids.
                //I.e. no boxes can be supported by small bricks or pyramids.
            } else if (o1.form == "box" && o2.size == "small" && (o2.form == "brick" || o2.form == "pyramid")) {
                return false;
                //Large boxes cannot be supported by large pyramids
                //Small pyramids can't support large anything
            } else if (o1.form == "box" && o1.size == "large" && o2.form == "pyramid") {
                return false;
            }
        }
        return true; 
    }


    function isAbove(ident1 : string, ident2: string, state: WorldState): boolean {
        var [x1, y1] = findPosition(ident1, state);
        var [x2, y2] = findPosition(ident2, state);
        return (x1==x2 && y2 < y1);
    }

    function isBeside(ident1: string, ident2: string, state: WorldState) : boolean {
        var [y1, x1] = findPosition(ident1, state);
        var [y2, x2] = findPosition(ident2, state);
        return (x1 - x2 == 1 || x1 - x2 == -1 );
    }

    function isOntop(ident1: string, ident2: string, state: WorldState): boolean {
        var [col1, row1] = findPosition(ident1, state);
        var [col2, row2] = findPosition(ident2, state);
        if (ident2 == "floor") {
            return row1 == 0;
        } else {
            return (row1 - row2 == 1 && col1 == col2);
        }
    }

    function findRelatedIdents(idents1: string[][], idents2: string[][], relation: string, state: WorldState): string[][]{
        var ret: string[][] = [];
        var leng1: number = idents1.length;
        var leng2: number = idents2.length; 
        for (var i = 0; i < leng1; i++) {
            for (var j =0; j < leng2; j++) {
                var l1 = idents1[i];
                var l2 = idents2[j];
                if (relation == "ontop" || relation == "inside") {
                    if (isOkSupport(l1[l1.length-1], l2[l2.length-1], state) 
                        && isOntop(l1[l1.length - 1], l2[l2.length - 1], state)) {
                        ret.push([l1[l1.length-1], l2[l2.length-1]]);
                    } 
                } else if (relation == "beside") {
                    if (isBeside(l1[l1.length-1], l2[l2.length-1], state)) {
                        ret.push([l1[l1.length-1], l2[l2.length-1]]);
                    }
                } else if (relation == "above") {
                    if (isAbove(l1[l1.length-1], l2[l2.length-1], state)) {
                        ret.push([l1[l1.length-1], l2[l2.length-1]]);
                    }
                }
            }
        }
        return ret;
    }
}

