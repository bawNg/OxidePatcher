﻿using System;
using System.IO;
using System.Linq;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace OxidePatcher.Patching
{
    /// <summary>
    /// Responsible for performing the actual patch process
    /// </summary>
    public class Patcher
    {
        /// <summary>
        /// Gets the project that this patcher will patch
        /// </summary>
        public Project PatchProject { get; private set; }

        /// <summary>
        /// Is this a Console or Window Patcher?
        /// </summary>
        public bool IsConsole { get; private set; }

        /// <summary>
        /// Called when a log message has been written
        /// </summary>
        public event Action<string> OnLogMessage;

        /// <summary>
        /// Initializes a new instance of the Patcher class
        /// </summary>
        /// <param name="patchproject"></param>
        /// <param name="console"></param>
        public Patcher(Project patchproject, bool console = false)
        {
            PatchProject = patchproject;
            IsConsole = console;
        }

        /// <summary>
        /// Gets the correct Assembly FilePath
        /// </summary>
        /// <param name="assemblyname"></param>
        /// <param name="original"></param>
        private string GetAssemblyFilename(string assemblyname, bool original)
        {
            if (original)
                return Path.Combine(PatchProject.TargetDirectory, Path.GetFileNameWithoutExtension(assemblyname) + "_Original" + Path.GetExtension(assemblyname));
            return Path.Combine(PatchProject.TargetDirectory, assemblyname);
        }

        /// <summary>
        /// Logs to console / window output and to log file
        /// </summary>
        /// <param name="format"></param>
        /// <param name="args"></param>
        internal void Log(string format, params object[] args)
        {
            var line = string.Format(format, args);
            WriteToLog(line);
            if (IsConsole) Console.WriteLine(line);
            else OnLogMessage?.Invoke(line);
        }

        /// <summary>
        /// Writes text to log file
        /// </summary>
        /// <param name="line"></param>
        private void WriteToLog(string line)
        {
            using (System.IO.StreamWriter file = new System.IO.StreamWriter("log.txt", true))
            {
                file.WriteLine(line);
            }
        }

        /// <summary>
        /// Performs the patch process
        /// </summary>
        public void Patch()
        {
            // Load oxide assembly
            string oxidefilename = Path.Combine(System.Windows.Forms.Application.StartupPath, "Oxide.Core.dll");
            if (!File.Exists(oxidefilename)) throw new FileNotFoundException("Failed to locate Oxide.dll assembly");
            AssemblyDefinition oxideassembly = AssemblyDefinition.ReadAssembly(oxidefilename);
            if (PatchProject == null)
                return;
            // CReate reader params
            ReaderParameters readerparams = new ReaderParameters();
            readerparams.AssemblyResolver = new AssemblyResolver { TargetDirectory = PatchProject.TargetDirectory };
            DateTime now = DateTime.Now;
            WriteToLog("----------------------------------------");
            WriteToLog(now.ToShortDateString() + " " + now.ToString("hh:mm:ss tt zzz"));
            WriteToLog("----------------------------------------");
            // Loop each manifest
            foreach (var manifest in PatchProject.Manifests)
            {
                // Get the assembly filename
                string filename;
                if (!IsConsole)
                {
                    filename = GetAssemblyFilename(manifest.AssemblyName, true);
                    if (!File.Exists(filename))
                    {
                        WriteToLog(string.Format("Failed to locate target assembly {0}", manifest.AssemblyName));
                        throw new FileNotFoundException(string.Format("Failed to locate target assembly {0}", manifest.AssemblyName), filename);
                    }
                }
                else
                {
                    filename = GetAssemblyFilename(manifest.AssemblyName, true);
                    if (!File.Exists(filename))
                    {
                        filename = GetAssemblyFilename(manifest.AssemblyName, false);
                        if (!File.Exists(filename))
                        {
                            WriteToLog(string.Format("Failed to locate target assembly {0}", manifest.AssemblyName));
                            throw new FileNotFoundException(string.Format("Failed to locate target assembly {0}", manifest.AssemblyName), filename);
                        }
                        else
                        {
                            System.IO.File.Copy(filename, Path.GetFileNameWithoutExtension(filename) + "_Original" + Path.GetExtension(filename), true);
                            filename = Path.GetFileNameWithoutExtension(filename) + "_Original" + Path.GetExtension(filename);
                        }
                    }
                }

                // Load it
                Log("Loading assembly {0}", manifest.AssemblyName);
                AssemblyDefinition assembly = AssemblyDefinition.ReadAssembly(filename, readerparams);

                var baseHooks = (from hook in manifest.Hooks where hook.BaseHook != null select hook.BaseHook).ToList();

                var enum_type = new TypeDefinition("Oxide", "GameHooks", TypeAttributes.Public | TypeAttributes.Sealed);
                enum_type.BaseType = assembly.MainModule.Import(typeof(Enum));
                assembly.MainModule.Types.Add(enum_type);

                var field = new FieldDefinition("value__", FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RTSpecialName, assembly.MainModule.TypeSystem.Int32);
                enum_type.Fields.Add(field);

                var hook_count = 0;

                // Loop each hook
                foreach (var hook in manifest.Hooks)
                {
                    if (baseHooks.Contains(hook)) continue;
                    // Check if it's flagged
                    if (hook.Flagged)
                    {
                        // Log
                        Log("Ignored hook {0} as it is flagged", hook.Name);
                    }
                    else
                    {
                        // Locate the method
                        MethodDefinition method;
                        try
                        {
                            var type = assembly.Modules
                                .SelectMany((m) => m.GetTypes())
                                .Single((t) => t.FullName == hook.TypeName);

                            method = type.Methods
                                .Single((m) => Utility.GetMethodSignature(m).Equals(hook.Signature));
                        }
                        catch (Exception)
                        {
                            WriteToLog(string.Format("Failed to locate method {0}::{1} in assembly {2}", hook.TypeName, hook.Signature.Name, manifest.AssemblyName));
                            throw new Exception(string.Format("Failed to locate method {0}::{1} in assembly {2}", hook.TypeName, hook.Signature.Name, manifest.AssemblyName));
                        }

                        // Let the hook do it's work
                        var weaver = new ILWeaver(method.Body) {Module = method.Module};
                        try
                        {
                            // Apply
                            bool patchApplied = hook.PreparePatch(method, weaver, oxideassembly, this) && hook.ApplyPatch(method, weaver, oxideassembly, this);
                            if (patchApplied)
                            {
                                Log("Applied hook {0} to {1}::{2}", hook.Name, hook.TypeName, hook.Signature.Name);
                                weaver.Apply(method.Body);
                                if (enum_type.Fields.All(f => f.Name != hook.HookName))
                                {
                                    field = new FieldDefinition(hook.HookName, FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault, enum_type);
                                    field.Constant = hook_count++;
                                    enum_type.Fields.Add(field);
                                }
                            }
                            else
                            {
                                Log("Failed to apply hook {0}", hook.Name);
                                Log("The injection index specified for {0} is invalid!", hook.Name);
                                hook.Flagged = true;
                            }
                        }
                        catch (Exception ex)
                        {
                            Log("Failed to apply hook {0}", hook.Name);
                            Log(ex.ToString());
                        }
                    }
                }

                field = new FieldDefinition("Count", FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault, enum_type);
                field.Constant = hook_count;
                enum_type.Fields.Add(field);

                // Save it
                Log("Saving assembly {0}", manifest.AssemblyName);
                filename = GetAssemblyFilename(manifest.AssemblyName, false);
                assembly.Write(filename);
            }
        }
    }
}
