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
 * Optimiser component that performs function inlining for arbitrary functions.
 */

#include <libjulia/optimiser/FullInliner.h>

#include <libjulia/optimiser/ASTCopier.h>

#include <libsolidity/inlineasm/AsmData.h>

#include <libsolidity/interface/Exceptions.h>

#include <libdevcore/CommonData.h>

#include <boost/range/adaptor/reversed.hpp>

using namespace std;
using namespace dev;
using namespace dev::julia;
using namespace dev::solidity;
using namespace dev::solidity::assembly;

void FullInliner::run()
{
	(*this)(m_block);
}

vector<Statement> FullInliner::operator()(FunctionalInstruction& _instr)
{
	vector<Statement> prefix;

	for (auto& arg: _instr.arguments | boost::adaptors::reversed)
	{
		vector<Statement> argPrefix = tryInline(arg);
		prefix += std::move(argPrefix);
		// Check that it actually moved.
		solAssert(argPrefix.empty(), "");
	}
	return prefix;
}

vector<Statement> FullInliner::operator()(FunctionCall&)
{
	solAssert(false, "Should have called tryInline instead.");
	return {};
}

vector<Statement> FullInliner::operator()(Assignment& _assignment)
{
	solAssert(_assignment.value, "");
	solUnimplementedAssert(_assignment.variableNames.size() == 1, "");
	return tryInline(*_assignment.value);
}

vector<Statement> FullInliner::operator()(VariableDeclaration& _varDecl)
{
	solUnimplementedAssert(_varDecl.variables.size() == 1, "");
	return tryInline(*_varDecl.value);
}

vector<Statement> FullInliner::operator()(If& _if)
{
	// Do not visit the condition because we cannot inline there.
	(*this)(_if.body);
	return {};
}

vector<Statement> FullInliner::operator()(Switch& _switch)
{
	// Do not visit the expression because we cannot inline there.
	for (auto& cse: _switch.cases)
		(*this)(cse.body);
	return {};
}

vector<Statement> FullInliner::operator()(FunctionDefinition& _funDef)
{
	m_functionScopes.insert(_funDef.name);
	(*this)(_funDef.body);
	solAssert(m_functionScopes.count(_funDef.name), "");
	m_functionScopes.erase(_funDef.name);
	return {};
}

vector<Statement> FullInliner::operator()(ForLoop& _loop)
{
	(*this)(_loop.pre);
	// Do not visit the condition because we cannot inline there.
	(*this)(_loop.post);
	(*this)(_loop.body);
	return {};
}

vector<Statement> FullInliner::operator()(Block& _block)
{
	// TODO: optimize the number of moves here.
	for (size_t i = 0; i < _block.statements.size(); ++i)
	{
		vector<Statement> data = tryInline(_block.statements.at(i));
		if (!data.empty())
		{
			size_t length = data.size();
			_block.statements.insert(
				_block.statements.begin() + i,
				std::make_move_iterator(data.begin()),
				std::make_move_iterator(data.end())
			);
			i += length;
		}
	}
	return {};
}

vector<Statement> FullInliner::tryInline(Statement& _statement)
{
	if (_statement.type() == typeid(FunctionCall))
	{
//		FunctionCall& funCall = boost::get<FunctionCall>(_statement);
//		bool allArgsPure = true;

//		for (auto& arg: funCall.arguments)
//			if (!tryInline(arg))
//				allArgsPure = false;
//		// TODO: Could this have distorted the code so that a simple replacement does not
//		// work anymore?

//		if (allArgsPure && m_inlinableFunctions.count(funCall.functionName.name))
//		{
//			FunctionDefinition const& fun = *m_inlinableFunctions.at(funCall.functionName.name);
//			map<string, Statement const*> replacements;
//			for (size_t i = 0; i < fun.arguments.size(); ++i)
//				replacements[fun.arguments[i].name] = &funCall.arguments[i];
//			_statement = replace(*boost::get<Assignment>(fun.body.statements.front()).value, replacements);

//			// TODO actually in the process of inlining, we could also make a funciton non-inlinable
//			// because it could now call itself

//			// Pureness of this depends on the pureness of the replacement,
//			// i.e. the pureness of the function itself.
//			// Perhaps we can just re-run?

//			// If two functions call each other, we have to exit after some iterations.

//			// Just return false for now.
//			return false;
//		}
//		else
//			return allArgsPure;
		return {};
	}
	else
		return boost::apply_visitor(*this, _statement);
}

Statement FullInliner::replace(Statement const& _statement, map<string, Statement const*> const& _replacements)
{
	if (_statement.type() == typeid(FunctionCall))
	{
		FunctionCall const& funCall = boost::get<FunctionCall>(_statement);
		vector<Statement> arguments;
		for (auto const& arg: funCall.arguments)
			arguments.push_back(replace(arg, _replacements));

		return FunctionCall{funCall.location, funCall.functionName, std::move(arguments)};
	}
	else if (_statement.type() == typeid(FunctionalInstruction))
	{
		FunctionalInstruction const& instr = boost::get<FunctionalInstruction>(_statement);
		vector<Statement> arguments;
		for (auto const& arg: instr.arguments)
			arguments.push_back(replace(arg, _replacements));

		return FunctionalInstruction{instr.location, instr.instruction, std::move(arguments)};
	}
	else if (_statement.type() == typeid(Identifier))
	{
		string const& name = boost::get<Identifier>(_statement).name;
		if (_replacements.count(name))
			return replace(*_replacements.at(name), {});
		else
			return _statement;
	}
	else if (_statement.type() == typeid(Literal))
		return _statement;

	solAssert(false, "");
	return {};
}
