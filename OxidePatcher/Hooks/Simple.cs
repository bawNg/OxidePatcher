using System;
using System.Collections.Generic;
using System.Linq;
using OxidePatcher.Patching;
using OxidePatcher.Views;

using Mono.Cecil;
using Mono.Cecil.Cil;

using AssemblyDefinition = Mono.Cecil.AssemblyDefinition;
using TypeDefinition = Mono.Cecil.TypeDefinition;

namespace OxidePatcher.Hooks
{
    public enum ReturnBehavior { Continue, ExitWhenValidType, ModifyRefArg, UseArgumentString }

    public enum ArgumentBehavior { None, JustThis, JustParams, All, UseArgumentString }

    /// <summary>
    /// A simple hook that injects at a certain point in the method, with a few options for handling arguments and return values
    /// </summary>
    [HookType("Simple", Default = true)]
    public class Simple : Hook
    {
        /// <summary>
        /// Gets or sets the instruction index to inject the hook call at
        /// </summary>
        public int InjectionIndex { get; set; }

        /// <summary>
        /// Gets or sets the return behavior
        /// </summary>
        public ReturnBehavior ReturnBehavior { get; set; }

        /// <summary>
        /// Gets or sets the argument behavior
        /// </summary>
        public ArgumentBehavior ArgumentBehavior { get; set; }

        /// <summary>
        /// Gets or sets the argument string
        /// </summary>
        public string ArgumentString { get; set; }

        /// <summary>
        /// Resolves assembly dependencies
        /// </summary>
        private DefaultAssemblyResolver resolver;

        public override bool ApplyPatch(MethodDefinition original, ILWeaver weaver, AssemblyDefinition oxideassembly, Patcher patcher = null)
        {
            // Start injecting where requested
            weaver.Pointer = InjectionIndex;

            // Get the existing instruction we're going to inject behind
            Instruction existing;
            try
            {
                existing = weaver.Instructions[weaver.Pointer];
            }
            catch (ArgumentOutOfRangeException)
            {
                ShowMsg(string.Format("The injection index specified for {0} is invalid!", Name), "Invalid Index", patcher);
                return false;
            }
            
            var dispatch_method = BuildDispatchMethod(patcher, weaver, oxideassembly, original.Module, original.DeclaringType, original, HookName);

            Instruction first_injected;
            if (ReturnBehavior == ReturnBehavior.ModifyRefArg)
            {
                var callhook = oxideassembly.MainModule.GetType("Oxide.Core.Interface").Methods.Single(m => m.IsStatic && m.Name == "CallHook");

                // Push the arguments array to the stack and make the call
                VariableDefinition argsvar;
                first_injected = PushArgsArray(original, weaver, out argsvar, patcher);
                var hookname = weaver.Add(Instruction.Create(OpCodes.Ldstr, HookName));
                if (first_injected == null) first_injected = hookname;
                if (argsvar != null)
                    weaver.Ldloc(argsvar);
                else
                    weaver.Add(Instruction.Create(OpCodes.Ldnull));
                weaver.Add(Instruction.Create(OpCodes.Call, original.Module.Import(callhook)));

                DealWithReturnValue(oxideassembly, original, argsvar, weaver);
            }
            else
            {
                VariableDefinition ret_var;
                ret_var = LoadDispatchArgs(original, weaver, patcher, out first_injected);
                weaver.Add(Instruction.Create(OpCodes.Call, dispatch_method));

                DealWithReturnValue(oxideassembly, original, null, weaver, ret_var);
            }

            // Find all instructions which pointed to the existing and redirect them
            for (int i = 0; i < weaver.Instructions.Count; i++)
            {
                Instruction ins = weaver.Instructions[i];
                if (ins.Operand != null && ins.Operand.Equals(existing))
                {
                    // Check if the instruction lies within our injection range
                    // If it does, it's an instruction we just injected so we don't want to edit it
                    if (i < InjectionIndex || i > weaver.Pointer)
                        ins.Operand = first_injected;
                }
            }
            return true;
        }

        private MethodDefinition BuildDispatchMethod(Patcher patcher, ILWeaver weaver, AssemblyDefinition oxideassembly, ModuleDefinition module, TypeDefinition type, MethodDefinition method, string name)
        {
            var parameter_types = new List<TypeReference>();

            var object_type = module.Import(typeof(object));
            var bool_type = module.Import(typeof(bool));

            // Are we going to use arguments?
            if (ArgumentBehavior != ArgumentBehavior.None)
            {
                // Are we using the argument string?
                if (ArgumentBehavior == ArgumentBehavior.UseArgumentString)
                {
                    string retvalue;
                    var args = ParseArgumentString(out retvalue);
                    if (args != null)
                    {
                        for (int i = 0; i < args.Length; i++)
                        {
                            string arg = args[i];
                            if (string.IsNullOrEmpty(arg))
                            {
                                parameter_types.Add(object_type);
                                continue;
                            }

                            var tokens = new string[0];
                            if (arg.Contains("."))
                            {
                                var parts = arg.Split('.');
                                arg = parts[0];
                                tokens = parts.Skip(1).ToArray();
                            }

                            var parameter_type = object_type;
                            if (arg == "this")
                            {
                                if (!method.IsStatic) parameter_type = type;
                            }
                            else if (arg[0] == 'p' || arg[0] == 'a')
                            {
                                int index;
                                if (int.TryParse(arg.Substring(1), out index))
                                    parameter_type = method.Parameters[index].ParameterType;
                            }
                            else if (arg[0] == 'l' || arg[0] == 'v')
                            {
                                int index;
                                if (int.TryParse(arg.Substring(1), out index))
                                    parameter_type = weaver.Variables[index].VariableType;
                            }

                            if (tokens.Length > 0)
                            {
                                parameter_type = GetFieldOrProperty(null, method, parameter_type.Resolve(), tokens, patcher);
                                if (parameter_type == null)
                                {
                                    //TODO: Show error?
                                    parameter_type = object_type;
                                }
                            }
                            
                            parameter_types.Add(parameter_type);
                        }
                    }
                }
                else
                {
                    // Figure out what we're doing
                    bool includeargs = ArgumentBehavior == ArgumentBehavior.All || ArgumentBehavior == ArgumentBehavior.JustParams;
                    bool includethis = ArgumentBehavior == ArgumentBehavior.All || ArgumentBehavior == ArgumentBehavior.JustThis;

                    if (includethis && !method.IsStatic) parameter_types.Add(type);

                    if (includeargs)
                    {
                        for (int i = 0; i < method.Parameters.Count; i++)
                        {
                            var parameter = method.Parameters[i];
                            if (!parameter.IsOut) parameter_types.Add(parameter.ParameterType);
                        }
                    }
                }
            }
            
            var attributes = MethodAttributes.CompilerControlled | MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig;
            var new_method = new MethodDefinition("Dispatch_" + name, attributes, module.Import(bool_type)) { DeclaringType = type };

            ParameterDefinition ret_parameter = null;
            if (method.ReturnType.MetadataType != MetadataType.Void)
            {
                var ret_type = new ByReferenceType(module.Import(method.ReturnType));
                ret_parameter = new ParameterDefinition(ret_type) { Name = "return_value", IsOut = true };
                new_method.Parameters.Add(ret_parameter);
            }

            foreach (var parameter_type in parameter_types)
            {
                new_method.Parameters.Add(new ParameterDefinition(parameter_type.Name.ToLower(), ParameterAttributes.None, module.Import(parameter_type)));
            }
            
            new_method.ImplAttributes = MethodImplAttributes.Managed;
            
            var body = new MethodBody(new_method);
            weaver = new ILWeaver(body) { Module = module };
            
            if (parameter_types.Count > 0)
            {
                var argsvar = weaver.AddVariable(new ArrayType(method.Module.TypeSystem.Object), "args");
                weaver.Add(ILWeaver.Ldc_I4_n(parameter_types.Count));
                weaver.Add(Instruction.Create(OpCodes.Newarr, method.Module.TypeSystem.Object));
                weaver.Stloc(argsvar);

                for (var i = 1; i < new_method.Parameters.Count; i++)
                {
                    var parameter = new_method.Parameters[i];
                    weaver.Ldloc(argsvar);
                    weaver.Add(ILWeaver.Ldc_I4_n(i - 1));
                    weaver.Add(ILWeaver.Ldarg(parameter));

                    if (parameter.ParameterType.IsByReference)
                    {
                        weaver.Add(Instruction.Create(OpCodes.Ldobj, parameter.ParameterType));
                        weaver.Add(Instruction.Create(OpCodes.Box, parameter.ParameterType));
                    }
                    else if (parameter.ParameterType.IsValueType)
                    {
                        weaver.Add(Instruction.Create(OpCodes.Box, parameter.ParameterType));
                    }

                    weaver.Add(Instruction.Create(OpCodes.Stelem_Ref));
                }

                weaver.Add(Instruction.Create(OpCodes.Ldstr, HookName));
                weaver.Ldloc(argsvar);
            }
            else
            {
                weaver.Add(Instruction.Create(OpCodes.Ldnull));
            }

            var callhook = oxideassembly.MainModule.GetType("Oxide.Core.Interface").Methods.Single(m => m.Name == "CallHook");
            weaver.Add(Instruction.Create(OpCodes.Call, module.Import(callhook)));

            if (ret_parameter != null)
            {
                var result = weaver.AddVariable(module.Import(module.TypeSystem.Object), "result");
                weaver.Stloc(result);

                weaver.Ldloc(result);

                // Check if the CallHook return is not null and matches the return type
                weaver.Add(Instruction.Create(OpCodes.Isinst, method.ReturnType));
                var i = weaver.Add(Instruction.Create(OpCodes.Ldnull));
                var skip_ret_handling = weaver.Add(Instruction.Create(OpCodes.Beq_S, i));

                // Unbox return and set it to the ret out parameter
                weaver.Ldloc(result);
                weaver.Add(Instruction.Create(OpCodes.Unbox_Any, method.ReturnType));
                weaver.Starg(ret_parameter);

                // Return true
                weaver.Add(Instruction.Create(OpCodes.Ldc_I4_1));
                weaver.Add(Instruction.Create(OpCodes.Ret));

                skip_ret_handling.Operand = weaver.Add(Instruction.Create(OpCodes.Ldc_I4_0));
            }
            else
            {
                weaver.Add(Instruction.Create(OpCodes.Ldc_I4_0));
            }
            
            weaver.Add(Instruction.Create(OpCodes.Ret));

            weaver.Apply(body);

            //body.SimplifyMacros(); //TODO: Add Cecil.Rocks if this is needed
            new_method.Body = body;
            type.Methods.Add(new_method);

            return new_method;
        }
        
        private Instruction PushArgsArray(MethodDefinition method, ILWeaver weaver, out VariableDefinition argsvar, Patcher patcher)
        {
            // Are we going to use arguments?
            if (ArgumentBehavior == ArgumentBehavior.None)
            {
                // Push null and we're done
                argsvar = null;
                return null;
            }

            // Create array variable
            Instruction firstInstruction;
            // Are we using the argument string?
            if (ArgumentBehavior == ArgumentBehavior.UseArgumentString)
            {
                string retvalue;
                string[] args = ParseArgumentString(out retvalue);
                if (args == null)
                {
                    // Silently fail, but at least produce valid IL
                    argsvar = null;
                    return null;
                }

                // Create the array
                argsvar = weaver.AddVariable(new ArrayType(method.Module.TypeSystem.Object), "args");
                firstInstruction = weaver.Add(ILWeaver.Ldc_I4_n(args.Length));
                weaver.Add(Instruction.Create(OpCodes.Newarr, method.Module.TypeSystem.Object));
                weaver.Stloc(argsvar);

                // Populate it
                for (var i = 0; i < args.Length; i++)
                {
                    var arg = args[i];
                    var target = ParseTargetString(ref arg);

                    weaver.Ldloc(argsvar);
                    weaver.Add(ILWeaver.Ldc_I4_n(i));
                    if (string.IsNullOrEmpty(arg))
                    {
                        weaver.Add(Instruction.Create(OpCodes.Ldnull));
                    }
                    else if (arg == "this")
                    {
                        if (method.IsStatic)
                            weaver.Add(Instruction.Create(OpCodes.Ldnull));
                        else
                            weaver.Add(ILWeaver.Ldarg(null));

                        GetFieldOrProperty(weaver, method, method.DeclaringType.Resolve(), target, patcher);
                    }
                    else if (arg[0] == 'p' || arg[0] == 'a')
                    {
                        int index;
                        if (int.TryParse(arg.Substring(1), out index))
                        {
                            ParameterDefinition pdef;

                            /*if (method.IsStatic)
                                pdef = method.Parameters[index];
                            else
                                pdef = method.Parameters[index + 1];*/
                            pdef = method.Parameters[index];

                            weaver.Add(ILWeaver.Ldarg(pdef));
                            if (pdef.ParameterType.IsByReference)
                            {
                                weaver.Add(Instruction.Create(OpCodes.Ldobj, pdef.ParameterType));
                                weaver.Add(Instruction.Create(OpCodes.Box, pdef.ParameterType));
                            }

                            if (GetFieldOrProperty(weaver, method, pdef.ParameterType.Resolve(), target, patcher) == null && pdef.ParameterType.IsValueType)
                                weaver.Add(Instruction.Create(OpCodes.Box, pdef.ParameterType));
                        }
                        else
                            weaver.Add(Instruction.Create(OpCodes.Ldnull));
                    }
                    else if (arg[0] == 'l' || arg[0] == 'v')
                    {
                        int index;
                        if (int.TryParse(arg.Substring(1), out index))
                        {
                            VariableDefinition vdef = weaver.Variables[index];

                            weaver.Ldloc(vdef);
                            if (vdef.VariableType.IsByReference)
                            {
                                weaver.Add(Instruction.Create(OpCodes.Ldobj, vdef.VariableType));
                                weaver.Add(Instruction.Create(OpCodes.Box, vdef.VariableType));
                            }

                            if (GetFieldOrProperty(weaver, method, vdef.VariableType.Resolve(), target, patcher) == null && vdef.VariableType.IsValueType)
                                weaver.Add(Instruction.Create(OpCodes.Box, vdef.VariableType));
                        }
                        else
                            weaver.Add(Instruction.Create(OpCodes.Ldnull));
                    }
                    else
                    {
                        weaver.Add(Instruction.Create(OpCodes.Ldnull));
                    }

                    weaver.Add(Instruction.Create(OpCodes.Stelem_Ref));
                }
            }
            else
            {
                // Figure out what we're doing
                bool includeargs = ArgumentBehavior == ArgumentBehavior.All || ArgumentBehavior == ArgumentBehavior.JustParams;
                bool includethis = ArgumentBehavior == ArgumentBehavior.All || ArgumentBehavior == ArgumentBehavior.JustThis;
                if (method.IsStatic) includethis = false;

                // Work out what arguments we're going to transmit
                List<ParameterDefinition> args = new List<ParameterDefinition>();
                if (includeargs)
                {
                    for (int i = 0; i < method.Parameters.Count; i++)
                    {
                        ParameterDefinition arg = method.Parameters[i];
                        if (!arg.IsOut)
                            args.Add(arg);
                    }
                }

                argsvar = weaver.AddVariable(new ArrayType(method.Module.TypeSystem.Object), "args");

                // Load arg count, create array, store
                if (includethis)
                    firstInstruction = weaver.Add(ILWeaver.Ldc_I4_n(args.Count + 1));
                else
                    firstInstruction = weaver.Add(ILWeaver.Ldc_I4_n(args.Count));
                weaver.Add(Instruction.Create(OpCodes.Newarr, method.Module.TypeSystem.Object));
                weaver.Stloc(argsvar);

                // Include this
                if (includethis)
                {
                    weaver.Ldloc(argsvar);
                    weaver.Add(ILWeaver.Ldc_I4_n(0));
                    weaver.Add(ILWeaver.Ldarg(null));
                    weaver.Add(Instruction.Create(OpCodes.Stelem_Ref));
                }

                // Loop each argument
                for (int i = 0; i < args.Count; i++)
                {
                    // Load array, load index load arg, store in array
                    ParameterDefinition arg = args[i];
                    weaver.Ldloc(argsvar);
                    if (includethis)
                        weaver.Add(ILWeaver.Ldc_I4_n(i + 1));
                    else
                        weaver.Add(ILWeaver.Ldc_I4_n(i));
                    weaver.Add(ILWeaver.Ldarg(args[i]));
                    if (arg.ParameterType.IsByReference)
                    {
                        weaver.Add(Instruction.Create(OpCodes.Ldobj, arg.ParameterType));
                        weaver.Add(Instruction.Create(OpCodes.Box, arg.ParameterType));
                    }
                    else if (arg.ParameterType.IsValueType)
                        weaver.Add(Instruction.Create(OpCodes.Box, arg.ParameterType));
                    weaver.Add(Instruction.Create(OpCodes.Stelem_Ref));
                }
            }
            return firstInstruction;
        }

        private VariableDefinition LoadDispatchArgs(MethodDefinition method, ILWeaver weaver, Patcher patcher, out Instruction first_instruction)
        {
            // Are we going to use arguments?
            if (ArgumentBehavior == ArgumentBehavior.None)
            {
                first_instruction = null;
                return null;
            }

            VariableDefinition ret_var = null;

            // Are we using the argument string?
            if (ArgumentBehavior == ArgumentBehavior.UseArgumentString)
            {
                string retvalue;
                string[] args = ParseArgumentString(out retvalue);
                if (args == null)
                {
                    // Silently fail, but at least produce valid IL
                    first_instruction = null;
                    return null;
                }

                ret_var = weaver.AddVariable(method.Module.Import(method.ReturnType), "return_value");

                // Load the ret local variable by reference onto the stack first
                first_instruction = weaver.Ldloc(ret_var);
                weaver.Add(Instruction.Create(OpCodes.Ldobj, ret_var.VariableType));

                // Load all arguments on the stack
                for (int i = 0; i < args.Length; i++)
                {
                    var arg = args[i];
                    var target = ParseTargetString(ref arg);

                    if (string.IsNullOrEmpty(arg))
                    {
                        weaver.Add(Instruction.Create(OpCodes.Ldnull));
                    }
                    else if (arg == "this")
                    {
                        if (method.IsStatic)
                            weaver.Add(Instruction.Create(OpCodes.Ldnull));
                        else
                            weaver.Add(ILWeaver.Ldarg(null));

                        GetFieldOrProperty(weaver, method, method.DeclaringType.Resolve(), target, patcher);
                    }
                    else if (arg[0] == 'p' || arg[0] == 'a')
                    {
                        int index;
                        if (int.TryParse(arg.Substring(1), out index))
                        {
                            ParameterDefinition pdef;

                            /*if (method.IsStatic)
                                pdef = method.Parameters[index];
                            else
                                pdef = method.Parameters[index + 1];*/
                            pdef = method.Parameters[index];

                            weaver.Add(ILWeaver.Ldarg(pdef));
                            if (pdef.ParameterType.IsByReference)
                            {
                                weaver.Add(Instruction.Create(OpCodes.Ldobj, pdef.ParameterType));
                                //weaver.Add(Instruction.Create(OpCodes.Box, pdef.ParameterType));
                            }

                            GetFieldOrProperty(weaver, method, pdef.ParameterType.Resolve(), target, patcher);
                        }
                        else
                        {
                            weaver.Add(Instruction.Create(OpCodes.Ldnull));
                        }
                    }
                    else if (arg[0] == 'l' || arg[0] == 'v')
                    {
                        int index;
                        if (int.TryParse(arg.Substring(1), out index))
                        {
                            VariableDefinition vdef = weaver.Variables[index];
                            weaver.Ldloc(vdef);
                            
                            if (vdef.VariableType.IsByReference)
                            {
                                weaver.Add(Instruction.Create(OpCodes.Ldobj, vdef.VariableType));
                                //weaver.Add(Instruction.Create(OpCodes.Box, vdef.VariableType));
                            }

                            GetFieldOrProperty(weaver, method, vdef.VariableType.Resolve(), target, patcher);
                        }
                        else
                        {
                            weaver.Add(Instruction.Create(OpCodes.Ldnull));
                        }
                    }
                    else
                    {
                        weaver.Add(Instruction.Create(OpCodes.Ldnull));
                    }
                }
            }
            else
            {
                ret_var = weaver.AddVariable(method.Module.Import(method.ReturnType), "return_value");

                // Load the ret local variable by reference onto the stack first
                first_instruction = weaver.Ldloc(ret_var);
                weaver.Add(Instruction.Create(OpCodes.Ldobj, ret_var.VariableType));

                // Figure out what we're doing
                var has_params = ArgumentBehavior == ArgumentBehavior.All || ArgumentBehavior == ArgumentBehavior.JustParams;
                var has_this = ArgumentBehavior == ArgumentBehavior.All || ArgumentBehavior == ArgumentBehavior.JustThis;
                if (method.IsStatic) has_this = false;

                // Work out what arguments we're going to include
                var parameters = new List<ParameterDefinition>();
                if (has_params)
                {
                    for (int i = 0; i < method.Parameters.Count; i++)
                    {
                        var parameter = method.Parameters[i];
                        if (!parameter.IsOut) parameters.Add(parameter);
                    }
                }
                
                if (has_this)
                {
                    first_instruction = weaver.Add(ILWeaver.Ldarg(null));
                }
                
                foreach (var arg in parameters)
                {
                    var instruction = weaver.Add(ILWeaver.Ldarg(arg));
                    if (first_instruction == null) first_instruction = instruction;
                    if (arg.ParameterType.IsByReference)
                    {
                        weaver.Add(Instruction.Create(OpCodes.Ldobj, arg.ParameterType));
                        //if (arg.ParameterType.Full?Name == "System.Object") weaver.Add(Instruction.Create(OpCodes.Box, arg.ParameterType));
                    }
                }
            }

            return ret_var;
        }


        private void DealWithReturnValue(AssemblyDefinition oxideassembly, MethodDefinition method, VariableDefinition argsvar, ILWeaver weaver, VariableDefinition ret_var = null)
        {
            // What return behavior do we use?
            switch (ReturnBehavior)
            {
                case ReturnBehavior.Continue:
                    // Just discard the return value
                    weaver.Add(Instruction.Create(OpCodes.Pop));
                    break;
                case ReturnBehavior.ExitWhenValidType:
                    // Is there a return value or not?
                    if (method.ReturnType.FullName == "System.Void")
                    {
                        // If the hook returned something that was non-null, return
                        Instruction i = weaver.Add(Instruction.Create(OpCodes.Ldnull));
                        weaver.Add(Instruction.Create(OpCodes.Beq_S, i.Next));
                        weaver.Add(Instruction.Create(OpCodes.Ret));
                    }
                    else
                    {
                        if (ret_var == null)
                        {
                            // Create variable
                            VariableDefinition returnvar = weaver.AddVariable(method.Module.TypeSystem.Object, "returnvar");

                            // Store the return value in it
                            weaver.Stloc(returnvar);
                            
                            weaver.Ldloc(returnvar);

                            // If it's non-null and matches the return type, return it - else continue
                            weaver.Add(Instruction.Create(OpCodes.Isinst, method.ReturnType));
                            Instruction i = weaver.Add(Instruction.Create(OpCodes.Ldnull));
                            weaver.Add(Instruction.Create(OpCodes.Beq_S, i.Next));

                            weaver.Ldloc(returnvar);
                            weaver.Add(Instruction.Create(OpCodes.Unbox_Any, method.ReturnType));
                            weaver.Add(Instruction.Create(OpCodes.Ret));
                        }
                        else
                        {
                            var jump_to_end = weaver.Add(Instruction.Create(OpCodes.Brfalse, weaver.Instructions[0]));
                            weaver.Ldloc(ret_var);
                            weaver.Add(Instruction.Create(OpCodes.Ret));
                            jump_to_end.Operand = weaver.Add(Instruction.Create(OpCodes.Ldnull)); //TODO: support value types
                            weaver.Add(Instruction.Create(OpCodes.Ret));
                        }
                    }
                    break;
                case ReturnBehavior.ModifyRefArg:
                    if (ret_var != null) throw new NotImplementedException("ReturnBehavior.ModifyRefArg not supported for fast dispatch methods");
                    string wayne;
                    var args = ParseArgumentString(out wayne);
                    if (args == null) break;
                    for (int i = 0; i < args.Length; i++)
                    {
                        string arg = args[i].ToLowerInvariant();
                        if (arg[0] == 'p' || arg[0] == 'a')
                        {
                            int index;
                            if (int.TryParse(arg.Substring(1), out index))
                            {
                                var pdef = method.Parameters[index];
                                if (pdef.ParameterType.IsValueType)
                                {
                                    weaver.Ldloc(argsvar);
                                    weaver.Add(ILWeaver.Ldc_I4_n(i));
                                    weaver.Add(Instruction.Create(OpCodes.Ldelem_Ref));
                                    weaver.Add(Instruction.Create(OpCodes.Unbox_Any, pdef.ParameterType));
                                    weaver.Starg(pdef);
                                }
                            }
                        }
                        else if (arg[0] == 'l' || arg[0] == 'v')
                        {
                            int index;
                            if (int.TryParse(arg.Substring(1), out index))
                            {
                                var vdef = weaver.Variables[index];
                                if (vdef.VariableType.IsValueType)
                                {
                                    weaver.Ldloc(argsvar);
                                    weaver.Add(ILWeaver.Ldc_I4_n(i));
                                    weaver.Add(Instruction.Create(OpCodes.Ldelem_Ref));
                                    weaver.Add(Instruction.Create(OpCodes.Unbox_Any, vdef.VariableType));
                                    weaver.Stloc(vdef);
                                }
                            }
                        }
                    }
                    weaver.Add(Instruction.Create(OpCodes.Pop));
                    break;
                case ReturnBehavior.UseArgumentString:
                    // Deal with it according to the retvalue of the arg string
                    string retvalue;
                    ParseArgumentString(out retvalue);
                    if (!string.IsNullOrEmpty(retvalue))
                    {
                        if (retvalue[0] == 'l' && retvalue.Length > 1)
                        {
                            int localindex;
                            if (int.TryParse(retvalue.Substring(1), out localindex))
                            {
                                var targetvar = weaver.Variables[localindex];

                                if (ret_var == null)
                                {
                                    var returnvar = weaver.AddVariable(method.Module.TypeSystem.Object, "returnvar");

                                    // Store the return value in it
                                    weaver.Stloc(returnvar);
                                    
                                    weaver.Ldloc(returnvar);

                                    // If it's non-null and matches the variable type, store it in the target variable
                                    weaver.Add(Instruction.Create(OpCodes.Isinst, targetvar.VariableType));
                                    Instruction i = weaver.Add(Instruction.Create(OpCodes.Ldnull));
                                    weaver.Add(Instruction.Create(OpCodes.Beq_S, i.Next));
                                    weaver.Ldloc(returnvar);
                                    weaver.Add(Instruction.Create(OpCodes.Unbox_Any, targetvar.VariableType));
                                    weaver.Stloc(targetvar);
                                }
                                else
                                {
                                    var jump_to_end = weaver.Add(Instruction.Create(OpCodes.Brfalse, weaver.Instructions[0]));
                                    weaver.Ldloc(targetvar);
                                    weaver.Add(Instruction.Create(OpCodes.Ret));
                                    jump_to_end.Operand = weaver.Add(Instruction.Create(OpCodes.Ldnull)); //TODO: support value types
                                    weaver.Add(Instruction.Create(OpCodes.Ret));
                                }

                                // Handled
                                return;
                            }
                        }
                        else if (retvalue[0] == 'a' && retvalue.Length > 1)
                        {
                            int localindex;
                            if (int.TryParse(retvalue.Substring(1), out localindex))
                            {
                                var targetvar = method.Parameters[localindex];

                                if (ret_var == null)
                                {
                                    var returnvar = weaver.AddVariable(method.Module.TypeSystem.Object, "returnvar");
                                    
                                    var byReferenceType = targetvar.ParameterType as ByReferenceType;
                                    TypeReference targettype = byReferenceType != null
                                        ? byReferenceType.ElementType
                                        : targetvar.ParameterType;

                                    // Store the return value in it
                                    weaver.Stloc(returnvar);
                                    
                                    weaver.Ldloc(returnvar);

                                    // If it's non-null and matches the variable type, store it in the target parameter variable
                                    weaver.Add(Instruction.Create(OpCodes.Isinst, targettype));
                                    Instruction i = weaver.Add(Instruction.Create(OpCodes.Ldnull));
                                    weaver.Add(Instruction.Create(OpCodes.Brfalse_S, i.Next));
                                    if (!targetvar.ParameterType.IsValueType)
                                        weaver.Add(ILWeaver.Ldarg(targetvar));
                                    weaver.Ldloc(returnvar);
                                    weaver.Add(Instruction.Create(OpCodes.Unbox_Any, targettype));
                                    if (!targetvar.ParameterType.IsValueType)
                                        weaver.Add(Instruction.Create(OpCodes.Stobj, targettype));
                                    else
                                        weaver.Starg(targetvar);
                                }
                                else
                                {
                                    var jump_to_end = weaver.Add(Instruction.Create(OpCodes.Brfalse, weaver.Instructions[0]));
                                    weaver.Add(ILWeaver.Ldarg(targetvar));
                                    weaver.Add(Instruction.Create(OpCodes.Ret));
                                    jump_to_end.Operand = weaver.Add(Instruction.Create(OpCodes.Ldnull)); //TODO: support value types
                                    weaver.Add(Instruction.Create(OpCodes.Ret));
                                }

                                // Handled
                                return;
                            }
                        }
                        else if (retvalue == "ret" || retvalue == "return")
                        {
                            if (ret_var == null)
                            {
                                // Create variable
                                VariableDefinition returnvar = weaver.AddVariable(method.Module.TypeSystem.Object, "returnvar");

                                // Store the return value in it
                                weaver.Stloc(returnvar);
                                
                                weaver.Ldloc(returnvar);

                                // If it's non-null and matches the return type, return it - else continue
                                weaver.Add(Instruction.Create(OpCodes.Isinst, method.ReturnType));
                                Instruction i = weaver.Add(Instruction.Create(OpCodes.Ldnull));
                                weaver.Add(Instruction.Create(OpCodes.Beq_S, i.Next));
                                weaver.Ldloc(returnvar);
                                weaver.Add(Instruction.Create(OpCodes.Unbox_Any, method.ReturnType));
                                weaver.Add(Instruction.Create(OpCodes.Ret));
                            }
                            else
                            {
                                var jump_to_end = weaver.Add(Instruction.Create(OpCodes.Brfalse, weaver.Instructions[0]));
                                weaver.Ldloc(ret_var);
                                weaver.Add(Instruction.Create(OpCodes.Ret));
                                jump_to_end.Operand = weaver.Add(Instruction.Create(OpCodes.Ldnull)); //TODO: support value types
                                weaver.Add(Instruction.Create(OpCodes.Ret));
                            }

                            // Handled
                            return;
                        }
                    }

                    // Not handled
                    weaver.Add(Instruction.Create(OpCodes.Pop));
                    break;
            }

        }

        private string[] ParseArgumentString(out string retvalue)
        {
            // Check arg string for null
            if (string.IsNullOrEmpty(ArgumentString))
            {
                retvalue = null;
                return null;
            }

            // Strip whitespace
            string argstr = new string(ArgumentString.Where((c) => !char.IsWhiteSpace(c)).ToArray());

            // Split by return value indicator
            string[] leftright = argstr.Split(new string[1] { "=>" }, StringSplitOptions.RemoveEmptyEntries);
            if (leftright.Length == 0)
            {
                retvalue = null;
                return null;
            }

            // Split by comma
            string[] args = leftright[0].Split(',').Select(arg => arg.ToLowerInvariant()).ToArray();

            // Set the return value
            if (leftright.Length > 1)
                retvalue = leftright[1];
            else
                retvalue = null;

            // Return
            return args;
        }

        private string[] ParseTargetString(ref string arg)
        {
            var target = new string[0];
            if (!string.IsNullOrEmpty(arg) && arg.Contains("."))
            {
                string[] split = arg.Split('.');
                arg = split[0];
                target = split.Skip(1).ToArray();
            }
            return target;
        }
        
        private TypeDefinition GetFieldOrProperty(ILWeaver weaver, MethodDefinition originalMethod, TypeDefinition currentArg, string[] target, Patcher patcher, bool boxed = true)
        {
            if (resolver == null)
            {
                resolver = new DefaultAssemblyResolver();
                resolver.AddSearchDirectory(patcher != null ? patcher.PatchProject.TargetDirectory : PatcherForm.MainForm.CurrentProject.TargetDirectory);
            }

            if (currentArg == null || target == null || target.Length == 0) return null;

            int i;
            var arg = currentArg;
            for (i = 0; i < target.Length; i++)
            {
                if (GetFieldOrProperty(weaver, originalMethod, ref arg, target[i])) continue;
                ShowMsg($"Could not find the field or property `{target[i]}` in any of the base classes or interfaces of `{currentArg.Name}`.", "Invalid field or property", patcher);
                break;
            }

            if (boxed && (arg.IsValueType || arg.IsByReference))
            {
                var type_reference = arg.Module == originalMethod.Module ? arg.Resolve() : originalMethod.Module.Import(arg.Resolve());
                weaver?.Add(Instruction.Create(OpCodes.Box, type_reference));
            }

            if (i >= 1) return arg;
            return null;
        }

        private bool GetFieldOrProperty(ILWeaver weaver, MethodDefinition originalMethod, ref TypeDefinition currentArg, string target)
        {
            if (currentArg == null || string.IsNullOrEmpty(target)) return false;

            while (currentArg != null)
            {
                if (currentArg.IsClass)
                {
                    if (currentArg.HasFields)
                    {
                        foreach (var field in currentArg.Fields)
                        {
                            if (!string.Equals(field.Name, target, StringComparison.CurrentCultureIgnoreCase)) continue;

                            weaver?.Add(field.Module == originalMethod.Module
                                ? Instruction.Create(OpCodes.Ldfld, field)
                                : Instruction.Create(OpCodes.Ldfld, originalMethod.Module.Import(field)));
                            currentArg = field.FieldType.Resolve();

                            return true;
                        }
                    }
                }

                if (currentArg.HasProperties)
                {
                    foreach (var property in currentArg.Properties)
                    {
                        if (!string.Equals(property.Name, target, StringComparison.CurrentCultureIgnoreCase)) continue;

                        weaver?.Add(property.GetMethod.Module == originalMethod.Module
                            ? Instruction.Create(OpCodes.Callvirt, property.GetMethod)
                            : Instruction.Create(OpCodes.Callvirt, originalMethod.Module.Import(property.GetMethod)));
                        currentArg = property.PropertyType.Resolve();

                        return true;
                    }
                }

                if (currentArg.HasInterfaces)
                {
                    foreach (var intf in currentArg.Interfaces)
                    {
                        var previousArg = currentArg;
                        currentArg = intf.Resolve();
                        if (GetFieldOrProperty(weaver, originalMethod, ref currentArg, target)) return true;
                        currentArg = previousArg;
                    }
                }

                currentArg = currentArg.BaseType?.Resolve();
            }

            return false;
        }

        public override HookSettingsControl CreateSettingsView()
        {
            return new SimpleHookSettingsControl { Hook = this };
        }
    }
}
