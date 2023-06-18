/*
* d4
* Copyright (C) 2020  Univ. Artois & CNRS
* 
* This program is free software: you can redistribute it and/or modify
* it under the terms of the GNU General Public License as published by
* the Free Software Foundation, either version 3 of the License, or
* (at your option) any later version.
* 
* This program is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
* GNU General Public License for more details.
* 
* You should have received a copy of the GNU General Public License
* along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/
#ifndef ManagerParserProblem_h
#define ManagerParserProblem_h

#include "../mtl/Vec.hh"
#include "../utils/SolverTypes.hh"

class ParserProblem
{
public:
  int parseCNF(char *benchName, vec<vec<Lit> > &clauses, vec<bool> &isProjectedVar, bool verb = true);
  void parseWeight(const char *fileWeights, vec<double> &weightLit, int nbVar);  
  int parseProblem(char *benchName, const char *fileWeights, vec<vec<Lit> > &clauses, vec<bool> &isProjectedVar, vec<double> &weightLit, bool verb = true);
};

#endif

