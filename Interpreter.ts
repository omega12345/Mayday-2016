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
        var parsesWithInterpretations : Parser.Command[] = [];
        parses.forEach((parseresult) => {
            try {
                var result : InterpretationResult = <InterpretationResult>parseresult;
                result.interpretation = interpretCommand(result.parse, currentState);
                interpretations.push(result);
                parsesWithInterpretations.push(parseresult.parse);
            } catch(err) {
                errors.push(err);
            }
        });
        if (interpretations.length>1)
            //Handles different interpretations as a result of multiple parse trees.
            verbalizeDifference (parsesWithInterpretations);
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
        var interpretation: DNFFormula = [];
        
        // 3 commands : take, move, put 
        if (cmd.command == "take") {
            var e: Parser.Entity = cmd.entity;
            var q: string = e.quantifier;
            var idents: string[] = find_solution(e.object, state).filter(i => i != "floor");
            console.log(idents);
            if (q == "any" || q == "a") {
				for (var i = 0; i < idents.length; i++) {
					interpretation.push([{ polarity: true, relation: "holding", args: [idents[i]] }]);
				}
            } else if (q == "the" ) {
				if (idents.length > 1) {
					throw new Error("clarify");
				} else if (idents.length == 0) {
					throw new Error("No such object."); // no satisfied identifier
				} else { 
					interpretation.push([{ polarity: true, relation: "holding", args: idents }]);
				}
            } else if (q == "all") {
				if (idents.length > 1) {
					throw new Error("can not take more than one object");
				} else if (idents.length == 1){
					interpretation.push([{ polarity: true, relation: "holding", args: idents }]);	
				} 
            }

        } else if (cmd.command == "move") {
            var e1: Parser.Entity = cmd.entity;
            var q1: string = e1.quantifier;
			var relation: string = cmd.location.relation;
            var e2: Parser.Entity = cmd.location.entity; 
            var q2: string = e2.quantifier;
            var idents1: string[] = find_solution(e1.object, state).filter(i => i != "floor");
            var idents2: string[] = find_solution(e2.object, state);
            
            if (q1 == "the" && idents1.length > 1) {
				throw new Error("clarify");
            } else if (q2 == "the" && idents2.length > 1) {
				throw new Error("clarify");
            } else { // no difference between 'the' and 'any'
                                
				if (q1 == "all" && q2 == "all") { // 'all' to 'all'
                                
					if(idents1.length == idents2.length && 
					   idents2.every(elem2 => idents1.every(elem1 => isOkRelation(elem1,elem2,relation,state)))) {
						var conj: Conjunction = [];
						for (var i = 0; i < idents2.length; i++) {
							if (idents1.every(elem1 => isOkRelation(elem1, idents2[i], relation, state))) {
								for (var j = 0; j < idents1.length; j++) {
									conj.push({ polarity: true, relation: relation, args: [idents1[i], idents2[j]] });
								}
							}
						}
					}
					if (conj.length != 0) {
						interpretation.push(conj);
					}
				} else if (q1 == "all" ) { // 'all' to 'any'
                                    
					var lists: string[][] = getAllLists(idents2, idents1.length);
					for (var j = 0; j < lists.length; j++) {
						var conj: Conjunction = [];
						for (var i = 0; i < idents1.length; i++) {
							if (isOkRelation(idents1[i], lists[j][i], relation, state)) {
								conj.push({ polarity: true, relation: relation, args: [idents1[i], lists[j][i]] });
							}
						}
						if (conj.length == idents1.length) {
							interpretation.push(conj);
						}
					}
				} else if (q2 == "all") { // 'any' to 'all'
					for (var i = 0; i < idents1.length; i++) {
						if (idents2.every(e => isOkRelation(idents1[i],e,relation,state))) {
							var conj: Conjunction = [];
							for (var j = 0; j < idents2.length; j++) {
								conj.push({ polarity: true, relation: relation, args: [idents1[i], idents2[j]] });
							}
							interpretation.push(conj);
						}
					}
				} else { // 'any' to 'any' 
					for (var i = 0; i < idents1.length; i++) {
                                                
						for (var j = 0; j < idents2.length; j++) {
                                                
							if (idents1[i] != idents2[j]) {
								if (isOkRelation(idents1[i], idents2[j], relation, state)) {								
									interpretation.push([{ polarity: true, relation: relation, args: [idents1[i], idents2[j]] }]);
								}
							}
						}
                                                
					} 
				}
                                    
            }
        }
        else if (cmd.command == "put") {
			if (state.holding == "") { //not holding anything. 
				throw new Error("not holding anything");
			} else {
				var hold_ident: string = state.holding;
				var loc: Parser.Location = cmd.location;
				var ent: Parser.Entity = loc.entity;
				var rel: string = loc.relation;
				var idents: string[] = find_solution(ent.object, state);
				if (idents.length == 1) {
					if (isOkRelation(hold_ident, idents[0], rel, state)) {
						interpretation.push([{ polarity: true, relation: relation, args: [hold_ident, idents[0]] }]);
					} else {
						throw new Error("can not move the holding object to the given location");
					}
				} else if (idents.length > 1) { 
					throw new Error("clarify");
				} else {
					throw new Error("Did not understand command");
				}
			}
        }
        if (interpretation.length == 0) {
            throw new Error("Failed to find an interpretation.");
        }
        return interpretation;
    }

    function find_solution(obj: Parser.Object, state: WorldState): string[]{
        if (IsSimpleObj(obj)) {
            return findIdents(obj, state);
          // if an object is not simple, then the object can always separate into 
          // two smaller objects, one quantifier and one relation .
        } else { 
            var [obj1,relation,quant,obj2] = separate_obj(obj);
            var idents1 = find_solution(obj1, state);
            var idents2 = find_solution(obj2, state);
            if (quant == "all") {
                var satisfied_idens1: string[] = satisfy_all(idents1, idents2, relation, state);
                return satisfied_idens1;
            } else if (quant == "any" || quant == "a") {
                return satisfy_any(idents1, idents2, relation, state);
            } else if (quant == "the") {
                //treat 'the' as same as 'any' 
                return satisfy_any(idents1, idents2, relation, state);
            } else {
				throw new Error("unidentified quantifier");
            }
        }
    }

    function satisfy_all(is1: string[], is2: string[], relation: string, state: WorldState): string[]{
        var ret: string[] = []; 
        for (var i = 0; i < is1.length; i++){
            var b: boolean = is2.every(elem => isTrueRelation(is1[i], elem, relation, state));
            if (b) {
                ret.push(is1[i]);
            }
        }
        return ret; 
    } 
    function satisfy_any(is1: string[], is2: string[], relation: string, state: WorldState): string[] {
        var ret: string[] = [];
        for (var i = 0; i < is1.length; i++) {
            var b: boolean = is2.some(elem => isTrueRelation(is1[i], elem, relation, state));
            if (b) {
                ret.push(is1[i]);
            }
        }
        return ret;
    } 

    /* checks if ident1 has a relation with ident2 */
    export function isTrueRelation(i1: string, i2: string, relation: string, state: WorldState) {    	
        if (relation == "ontop") {
            return isOntop(i1, i2, state);
        } else if (relation == "inside") {
            return isInside(i1, i2, state);
        } else if (relation == "beside") {
            return (isBeside(i1, i2, state))
        } else if (relation == "above") {
            return (isAbove(i1, i2, state))
        } else if (relation == "under") {
            return (isUnder(i1, i2, state));
        } else if (relation == "leftof") {
            return isLeftof(i1, i2, state);
        } else if (relation == "rightof") {
            return isRightof(i1, i2, state);
        } else {
            throw "Found unknown relation: " + relation;
        }
    }
 
    function separate_obj(obj: Parser.Object): [Parser.Object, string, string, Parser.Object] {
        var location = obj.location;
        var ent = location.entity;
        return [obj.object, location.relation, ent.quantifier, ent.object];
    }

    function IsSimpleObj(obj: Parser.Object): Boolean {
        if (obj.object == null) {
            return true;
        } else {
            return false;
        }
    }

    /* checks if object1 can be supported by object2 */  
    export function isOkSupport(o1: Parser.Object, o2: Parser.Object): boolean {
            //Balls must be in boxes or on the floor, otherwise they roll away.
            if (o1.form == "ball" && o2.form != "box" && o2.form != "floor") {
                return false;
            } else if (o2.form == "ball") { //Balls cannot support anything.
                return false;
                //Small objects cannot support large objects
            } else if (o1.size == "large" && o2.size == "small") {
                return false;
                //Boxes cannot contain pyramids, planks or boxes of the same size.  
            } else if (o2.form == "box" && o2.size == o1.size && (o1.form == "pyramid" || o1.form == "plank" || o1.form == "box")) {
                return false;
                //Small boxes cannot be supported by small bricks or pyramids.
                //I.e. no boxes can be supported by small bricks or pyramids.
            } else if (o1.form == "box" && o2.size == "small" && (o2.form == "brick" || o2.form == "pyramid")) {
                return false;
                //Large boxes cannot be supported by large pyramids
                //Small pyramids can't support large anything
            } else if (o1.form == "box" && o1.size == "large" && o2.form == "pyramid") {
                return false;
            } else {
				return true;
            }
    }

    /* checks if ident1 can have a relation with ident2 
       for instance, a ball on a box -> false realtion */
    function isOkRelation(ident1: string, ident2: string, rel: string, state: WorldState): boolean {
        // if ident1 == "floor" ???? 
        if (ident2 == "floor" && rel == "ontop") {
			return true;
        } else if (ident2 == "floor" && rel != "ontop") {
			return false;
        } else {
			var o1: Parser.Object = state.objects[ident1];
			var o2: Parser.Object = state.objects[ident2];
			if (rel == "inside") {
				if (o2.form == "box") {
					return isOkSupport(o1, o2);
				} else {
					return false;
				}
			} else if (rel == "ontop") {
				if (o2.form == "box") {
					return false;
				} else {
					return isOkSupport(o1, o2);
				}

			} else {
				return true;
			}
        }
    }


    export function isAbove(ident1: string, ident2: string, state: WorldState): boolean {
        var [col1, row1] = findPosition(ident1, state);
        var [col2, row2] = findPosition(ident2, state);
        if (col1 == col2 && row2 < row1) {
            return true;
        } else {
            return false;
        }
    }
    export function isUnder(ident1: string, ident2: string, state: WorldState): boolean {
        var [col1, row1] = findPosition(ident1, state);
        var [col2, row2] = findPosition(ident2, state);
        if (col1 == col2 && row1 < row2) {
            return true;
        } else {
            return false;
        }
    }
    export function isBeside(ident1: string, ident2: string, state: WorldState): boolean {
        var [col1, row1] = findPosition(ident1, state);
        var [col2, row2] = findPosition(ident2, state);
        if ((col1 - col2 == 1 && row1 == row2) || (col1 - col2 == -1 && row1 == row2)) {
            return true;
        } else {
            return false;
        }
    }

    export function isInside(ident1: string, ident2: string, state: WorldState): boolean {
        if (state.objects[ident2].form == "box") { //Objects are “inside” boxes
            var [col1, row1] = findPosition(ident1, state);
            var [col2, row2] = findPosition(ident2, state);
            if (row1 - row2 == 1 && col1 == col2) {
                return true;
            } else {
                return false;
            }
        } else {
            return false;
        }
    }
    export function isOntop(ident1: string, ident2: string, state: WorldState): boolean {
        if (ident2 == "floor") {
            var [col1, row1] = findPosition(ident1, state);
            return row1 == 0;
        } else if (state.objects[ident2].form == "box") {
            return false;
        } else {
            var [col1, row1] = findPosition(ident1, state);
            var [col2, row2] = findPosition(ident2, state);
            if (row1 - row2 == 1 && col1 == col2) {
                return true;
            } else {
                return false;
            }
        }
    }
    export function isLeftof(ident1: string, ident2: string, state: WorldState): boolean {
        var [col1, row1] = findPosition(ident1, state);
        var [col2, row2] = findPosition(ident2, state);
        if (col1 < col2) {
            return true;
        } else {
            return false;
        }
    }
    export function isRightof(ident1: string, ident2: string, state: WorldState): boolean {
        var [col1, row1] = findPosition(ident1, state);
        var [col2, row2] = findPosition(ident2, state);
        if (col1 > col2) {
            return true;
        } else {
            return false;
        }
    }


    /* find identifiers that satisfy the object description */
    function findIdents(o: Parser.Object, state: WorldState): string[] {
        var objects: string[] = Array.prototype.concat.apply([], state.stacks);
        var n: number = objects.length;
        var idents: string[] = [];
        if (o.form == "floor") {
            idents.push("floor");
        } else {
            for (var i = 0; i < n; i++) {
                if (objectMatch(o, state.objects[objects[i]])) {
                    idents.push(objects[i]);
                }
            }
        }
        return idents;
    }

    function objectMatch(o1: Parser.Object, o2: Parser.Object): boolean {
        var ret = ((o1.color == null || o1.color == o2.color)
            && (o1.size == null || o1.size == o2.size)
            && (o1.form == "anyform" || o1.form == o2.form));
        return ret;
    }

    /* find an identifier position in a world, return [column, row]. */
    function findPosition(ident: string, state: WorldState): number[] {
        var pos: number[] = []
        var stacks: Stack[] = state.stacks;
        var col: number = 0;
        var row: number = 0;
        for (var i = 0; i < stacks.length; i++) {
            for (var j = 0; j < stacks[i].length; j++) {
                if (stacks[i][j] == ident) {
                    col = i;
                    row = j;
                }
            }
        }
        return [col, row];
    }
    /* return all possible combination of a given list. 
       for instance if input elements = ["a","b"], and leng = 2, 
       then getAllLists will return [["a","a"],["a","b"],["b","a"],["b","b"]] */
	function getAllLists(elements: string[], leng: number): string[][] {
		var allLists: string[][] = [];
		if (leng == 1) {
			var ret: string[][] = [];
			for (var i = 0; i < elements.length; i++) {
				ret.push([elements[i]]);
			}
			return ret;
		} else {
			var allSublists: string[][] = getAllLists(elements, leng - 1);
			for (var i = 0; i < elements.length; i++) {
				for (var j = 0; j < allSublists.length; j++) {
					var l: string[] = [];
					l.push(elements[i]);
					for (var s = 0; s < allSublists[j].length; s++) {
						l.push(allSublists[j][s]);
					}
					allLists.push(l);
				}
			}
		}
		return allLists;
    }

    //If the results in the list differ, throws an error describing the difference.
    //Otherwise, does nothing.
    function verbalizeDifference(input : Parser.Command[]) : void {
        
        throw "Your statement is ambiguous. Please clarify.";
    }

}
/*

Thing to check:
- put-commmand !!
- floor handling is okey ?
- 

*/




