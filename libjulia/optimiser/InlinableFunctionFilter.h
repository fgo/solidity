/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
/**
 * Optimiser component that identifies functions to be inlined.
 */

#pragma once

#include <libjulia/ASTDataForward.h>

#include <libsolidity/interface/Exceptions.h>

#include <set>

namespace dev
{
namespace julia
{

/**
 * Optimiser component that finds functions that can be
 * inlined inside functional expressions, i.e. functions that
 *  - have a single return parameter r
 *  - have a body like r := <functional expression>
 *  - neither reference themselves nor r in the right hand side
 *
 * This component can only be used on sources with unique names.
 */
class InlinableFunctionFilter: public boost::static_visitor<bool>
{
public:

	std::map<std::string, FunctionDefinition const*> const& inlinableFunctions() const
	{
		return m_inlinableFunctions;
	}

	bool operator()(Literal const&) { return true; }
	bool operator()(Instruction const&) { return true; }
	bool operator()(Identifier const& _identifier);
	bool operator()(FunctionalInstruction const& _instr);
	bool operator()(FunctionCall const& _funCall);
	bool operator()(Label const&) { solAssert(false, ""); }
	bool operator()(StackAssignment const&) { solAssert(false, ""); }
	bool operator()(Assignment const&) { return false; }
	bool operator()(VariableDeclaration const&) { return false; }
	bool operator()(If const& _if);
	bool operator()(Switch const& _switch);
	bool operator()(FunctionDefinition const& _function);

	bool operator()(ForLoop const& _loop);

	bool operator()(Block const& _block);

private:
	bool allowed(std::string const& _name) const
	{
		return m_disallowedIdentifiers.count(_name) == 0;
	}

	bool all(std::vector<Statement> const& _statements);

	std::set<std::string> m_disallowedIdentifiers;
	std::map<std::string, FunctionDefinition const*> m_inlinableFunctions;
};

}
}
