/*
* Copyright 2024 Rochus Keller <mailto:me@rochus-keller.ch>
*
* This file is part of the BUSY build system.
*
* The following is the license that applies to this copy of the
* application. For a license to use the application under conditions
* other than those described here, please email to me@rochus-keller.ch.
*
* GNU General Public License Usage
* This file may be used under the terms of the GNU General Public
* License (GPL) versions 2.0 or 3.0 as published by the Free Software
* Foundation and appearing in the file LICENSE.GPL included in
* the packaging of this file. Please review the following information
* to ensure GNU General Public Licensing requirements will be met:
* http://www.fsf.org/licensing/licenses/info/GPLv2.html and
* http://www.gnu.org/copyleft/gpl.html.
*/

/* This is a table-reading generator in the vein of bsqmakegen.c. In contrast to the qmake generator
 * it does not have to accumulate object files and forward dependency libraries, since CMake's target
 * model does transitive dependency propagation itself via target_link_libraries and the
 * PUBLIC/PRIVATE/INTERFACE usage requirement scopes. The result is a single, self-contained
 * CMakeLists.txt written to the source root, which can be built stand-alone or consumed from another
 * CMake project via add_subdirectory() thanks to the emitted namespaced ALIAS targets.
 * The output is specific to the platform/toolchain BUSY was analyzed for (like the qmake generator). */

#include "bscmakegen.h"
#include "bsrunner.h"
#include "bshost.h"
#include "bsparser.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include "lauxlib.h"

typedef enum BS_Class { BS_NoClass, BS_LibraryClass, BS_ExecutableClass, BS_SourceSetClass,
                        BS_GroupClass, BS_ConfigClass,
                        BS_LuaScriptClass, BS_LuaScriptForEachClass, BS_CopyClass, BS_MessageClass,
                        BS_MocClass, BS_RccClass, BS_UicClass } BS_Class;

static void addPath(lua_State* L, int lhs, int rhs)
{
    if( *lua_tostring(L,rhs) == '/' )
        lua_pushvalue(L, rhs);
    else if( bs_add_path(L,lhs,rhs) )
        luaL_error(L,"creating absolute path from provided root gives an error: %s %s",
                   lua_tostring(L,lhs), lua_tostring(L,rhs) );
}

static int isa(lua_State* L, int builtins, int cls, const char* what )
{
    lua_getfield(L,builtins,what);
    const int res = bs_isa(L,-1,cls);
    lua_pop(L,1);
    return res;
}

static int getClass(lua_State* L, int prodinst, int builtins)
{
    lua_getmetatable(L,prodinst);
    const int cls = lua_gettop(L);
    int res = BS_NoClass;
    if( isa( L, builtins, cls, "Library" ) )
        res = BS_LibraryClass;
    else if( isa( L, builtins, cls, "Executable") )
        res = BS_ExecutableClass;
    else if( isa( L, builtins, cls, "SourceSet") )
        res = BS_SourceSetClass;
    else if( isa( L, builtins, cls, "Group") )
        res = BS_GroupClass;
    else if( isa( L, builtins, cls, "Config") )
        res = BS_ConfigClass;
    else if( isa( L, builtins, cls, "LuaScript") )
        res = BS_LuaScriptClass;
    else if( isa( L, builtins, cls, "LuaScriptForeach") )
        res = BS_LuaScriptForEachClass;
    else if( isa( L, builtins, cls, "Copy") )
        res = BS_CopyClass;
    else if( isa( L, builtins, cls, "Message") )
        res = BS_MessageClass;
    else if( isa( L, builtins, cls, "Moc") )
        res = BS_MocClass;
    else if( isa( L, builtins, cls, "Rcc") )
        res = BS_RccClass;
    else if( isa( L, builtins, cls, "Uic") )
        res = BS_UicClass;
    lua_pop(L,1); // cls
    return res;
}

static const char* getClassName(int cls)
{
    switch( cls )
    {
    case BS_LibraryClass: return "Library";
    case BS_ExecutableClass: return "Executable";
    case BS_SourceSetClass: return "SourceSet";
    case BS_GroupClass: return "Group";
    case BS_ConfigClass: return "Config";
    case BS_LuaScriptClass: return "LuaScript";
    case BS_LuaScriptForEachClass: return "LuaScriptForEach";
    case BS_CopyClass: return "Copy";
    case BS_MessageClass: return "Message";
    case BS_MocClass: return "Moc";
    case BS_RccClass: return "Rcc";
    case BS_UicClass: return "Uic";
    default: return "<unknown>";
    }
}

/* linearize the dependency graph depth-first, deps before dependents, marking each decl with #cmake
 * so we visit each product exactly once and reference already-defined targets */

static int mark(lua_State* L) // args: productinst, order; no returns
{
    const int inst = 1;
    const int order = 2;
    const int top = lua_gettop(L);

    lua_getfield(L,inst,"#decl");
    const int decl = lua_gettop(L);

    lua_getfield(L,decl,"#cmake");
    if( lua_isnil(L,-1) )
    {
        bs_declpath(L,decl,"."); // dotted path, unique across modules and valid as a CMake target name
        lua_setfield(L,decl,"#cmake");
    }else
    {
        lua_pop(L,2); // decl, #cmake
        return 0;
    }
    lua_pop(L,1); // #cmake

    lua_getfield(L,inst,"deps");
    const int deps = lua_gettop(L);
    if( lua_isnil(L,deps) )
    {
        lua_pop(L,2); // deps, decl
        return 0;
    }

    const int ndeps = lua_objlen(L,deps);
    int i;
    for( i = 1; i <= ndeps; i++ )
    {
        lua_pushcfunction(L, mark);
        lua_rawgeti(L,deps,i);
        lua_pushvalue(L,order);
        lua_call(L,2,0);
    }
    lua_pop(L,1); // deps

    lua_pushvalue(L,decl);
    lua_rawseti(L,order,lua_objlen(L,order)+1 );

    lua_pop(L,1); // decl

    assert( top == lua_gettop(L) );
    return 0;
}

/* push the CMake target name of a product decl */
static void pushTargetName(lua_State* L, int decl)
{
    lua_getfield(L,decl,"#cmake");
    if( lua_isnil(L,-1) )
    {
        lua_pop(L,1);
        bs_declpath(L,decl,".");
    }
}

/* resolve a BUSY source/include path to a relocatable CMake path expression and push it as a string.
 * relative paths become ${CMAKE_CURRENT_SOURCE_DIR}/... , paths inside the BUSY build dir become
 * ${CMAKE_CURRENT_BINARY_DIR}/... , everything else stays absolute (normalized, forward slashes) */
static void pushResolvedPath(lua_State* L, int inst, int builtins, int pathIdx)
{
    const int top = lua_gettop(L);

    lua_getfield(L,builtins,"#inst");
    const int binst = lua_gettop(L);
    lua_getfield(L,binst,"root_source_dir");
    const int srcRoot = lua_gettop(L);
    lua_getfield(L,binst,"root_build_dir");
    const int bldRoot = lua_gettop(L);

    if( *lua_tostring(L,pathIdx) == '/' )
        lua_pushvalue(L,pathIdx);
    else
    {
        bs_getModuleVar(L,inst,"#dir");
        addPath(L,lua_gettop(L),pathIdx);
        lua_remove(L,-2); // remove #dir, keep abs
    }
    const int abs = lua_gettop(L);

    const size_t bldlen = strlen(lua_tostring(L,bldRoot));
    if( strncmp(lua_tostring(L,bldRoot),lua_tostring(L,abs),bldlen) == 0 )
        lua_pushfstring(L,"${CMAKE_CURRENT_BINARY_DIR}%s", lua_tostring(L,abs)+bldlen);
    else if( bs_makeRelative(lua_tostring(L,srcRoot),lua_tostring(L,abs)) == BS_OK )
        lua_pushfstring(L,"${CMAKE_CURRENT_SOURCE_DIR}/%s", bs_global_buffer());
    else
        lua_pushvalue(L,abs);

    lua_replace(L,binst); // move result down to the binst slot
    lua_pop(L,3); // srcRoot, bldRoot, abs

    assert( lua_gettop(L) == top + 1 );
}

/* emit sources of inst (one per line, quoted); returns the number written */
static int addSources(lua_State* L, int inst, int builtins, FILE* out)
{
    const int top = lua_gettop(L);

    lua_getfield(L,inst,"sources");
    const int sources = lua_gettop(L);
    const size_t n = lua_objlen(L,sources);
    size_t i;
    for( i = 1; i <= n; i++ )
    {
        lua_rawgeti(L,sources,i);
        pushResolvedPath(L,inst,builtins,lua_gettop(L));
        if( out ) fprintf(out,"    \"%s\"\n", lua_tostring(L,-1));
        lua_pop(L,2); // source, resolved
    }
    lua_pop(L,1); // sources

    assert( top == lua_gettop(L) );
    return (int)n;
}

/* recursively collect include dirs from inst and its configs; when out is NULL only counts.
 * returns the number of entries */
static int addIncludes(lua_State* L, int inst, int builtins, FILE* out)
{
    const int top = lua_gettop(L);
    int n = 0;

    lua_getfield(L,inst,"configs");
    const int configs = lua_gettop(L);
    size_t i;
    for( i = 1; i <= lua_objlen(L,configs); i++ )
    {
        lua_rawgeti(L,configs,i);
        n += addIncludes(L,lua_gettop(L),builtins,out);
        lua_pop(L,1);
    }
    lua_pop(L,1); // configs

    lua_getfield(L,inst,"include_dirs");
    const int includes = lua_gettop(L);
    for( i = 1; i <= lua_objlen(L,includes); i++ )
    {
        lua_rawgeti(L,includes,i);
        pushResolvedPath(L,inst,builtins,lua_gettop(L));
        if( out ) fprintf(out,"    \"%s\"\n", lua_tostring(L,-1));
        lua_pop(L,2); // include, resolved
        n++;
    }
    lua_pop(L,1); // includes

    assert( top == lua_gettop(L) );
    return n;
}

/* recursively collect defines from inst and its configs; when out is NULL only counts */
static int addDefines(lua_State* L, int inst, FILE* out)
{
    const int top = lua_gettop(L);
    int n = 0;

    lua_getfield(L,inst,"configs");
    const int configs = lua_gettop(L);
    size_t i;
    for( i = 1; i <= lua_objlen(L,configs); i++ )
    {
        lua_rawgeti(L,configs,i);
        n += addDefines(L,lua_gettop(L),out);
        lua_pop(L,1);
    }
    lua_pop(L,1); // configs

    lua_getfield(L,inst,"defines");
    const int defines = lua_gettop(L);
    for( i = 1; i <= lua_objlen(L,defines); i++ )
    {
        lua_rawgeti(L,defines,i);
        // a CMake quoted string keeps an embedded \" as an escaped quote, so we can pass the raw define
        if( out ) fprintf(out,"    \"%s\"\n", lua_tostring(L,-1));
        lua_pop(L,1);
        n++;
    }
    lua_pop(L,1); // defines

    assert( top == lua_gettop(L) );
    return n;
}

/* recursively collect a flag list field from inst and its configs, wrapping each flag in wrap
 * (wrap uses %s for the flag, e.g. "%s" or "$<$<COMPILE_LANGUAGE:C>:%s>"); when out is NULL only counts */
static int addFlags(lua_State* L, int inst, FILE* out, const char* field, const char* wrap)
{
    const int top = lua_gettop(L);
    int n = 0;

    lua_getfield(L,inst,"configs");
    const int configs = lua_gettop(L);
    size_t i;
    for( i = 1; i <= lua_objlen(L,configs); i++ )
    {
        lua_rawgeti(L,configs,i);
        n += addFlags(L,lua_gettop(L),out,field,wrap);
        lua_pop(L,1);
    }
    lua_pop(L,1); // configs

    lua_getfield(L,inst,field);
    const int flags = lua_gettop(L);
    for( i = 1; i <= lua_objlen(L,flags); i++ )
    {
        lua_rawgeti(L,flags,i);
        lua_pushfstring(L,wrap,lua_tostring(L,-1));
        if( out ) fprintf(out,"    \"%s\"\n", lua_tostring(L,-1));
        lua_pop(L,2);
        n++;
    }
    lua_pop(L,1); // flags

    assert( top == lua_gettop(L) );
    return n;
}

/* recursively collect external library search dirs, names and frameworks from inst and its configs;
 * when out is NULL only counts */
static int addExtLibs(lua_State* L, int inst, int builtins, FILE* out)
{
    const int top = lua_gettop(L);
    int n = 0;

    lua_getfield(L,inst,"configs");
    const int configs = lua_gettop(L);
    size_t i;
    for( i = 1; i <= lua_objlen(L,configs); i++ )
    {
        lua_rawgeti(L,configs,i);
        n += addExtLibs(L,lua_gettop(L),builtins,out);
        lua_pop(L,1);
    }
    lua_pop(L,1); // configs

    lua_getfield(L,inst,"lib_dirs");
    const int ldirs = lua_gettop(L);
    for( i = 1; i <= lua_objlen(L,ldirs); i++ )
    {
        lua_rawgeti(L,ldirs,i);
        pushResolvedPath(L,inst,builtins,lua_gettop(L));
        if( out ) fprintf(out,"    \"-L%s\"\n", lua_tostring(L,-1));
        lua_pop(L,2);
        n++;
    }
    lua_pop(L,1); // ldirs

    lua_getfield(L,inst,"lib_names");
    const int lnames = lua_gettop(L);
    for( i = 1; i <= lua_objlen(L,lnames); i++ )
    {
        lua_rawgeti(L,lnames,i);
        if( out ) fprintf(out,"    \"%s\"\n", lua_tostring(L,-1));
        lua_pop(L,1);
        n++;
    }
    lua_pop(L,1); // lnames

    lua_getfield(L,inst,"frameworks");
    const int fworks = lua_gettop(L);
    for( i = 1; i <= lua_objlen(L,fworks); i++ )
    {
        lua_rawgeti(L,fworks,i);
        if( out ) fprintf(out,"    \"-framework\" \"%s\"\n", lua_tostring(L,-1));
        lua_pop(L,1);
        n++;
    }
    lua_pop(L,1); // fworks

    lua_getfield(L,inst,"lib_files");
    const int lfiles = lua_gettop(L);
    for( i = 1; i <= lua_objlen(L,lfiles); i++ )
    {
        lua_rawgeti(L,lfiles,i);
        pushResolvedPath(L,inst,builtins,lua_gettop(L));
        if( out ) fprintf(out,"    \"%s\"\n", lua_tostring(L,-1));
        lua_pop(L,2);
        n++;
    }
    lua_pop(L,1); // lfiles

    assert( top == lua_gettop(L) );
    return n;
}

/* Collect the transitive closure of *object-producing* dependencies (source sets and moc/rcc/uic
 * object libraries), descending through groups and through other object libraries, but stopping at
 * real static/shared libraries (their objects are already archived inside them). Deduplicated via the
 * visited table (keyed by target name). These are linked PRIVATE into the absorbing target so their
 * objects are archived exactly once - this mirrors qmake, where source sets are forwarded to the final
 * executable/shared lib rather than merged into intermediate static libraries. When out is NULL only counts. */
static int addObjectDeps(lua_State* L, int inst, int builtins, int visited, FILE* out)
{
    const int top = lua_gettop(L);
    int n = 0;

    lua_getfield(L,inst,"deps");
    const int deps = lua_gettop(L);
    if( !lua_isnil(L,deps) )
    {
        size_t i;
        for( i = 1; i <= lua_objlen(L,deps); i++ )
        {
            lua_rawgeti(L,deps,i);
            const int dep = lua_gettop(L);
            const int cls = getClass(L,dep,builtins);
            if( cls == BS_GroupClass )
                n += addObjectDeps(L,dep,builtins,visited,out);
            else if( cls == BS_SourceSetClass || cls == BS_MocClass ||
                    cls == BS_RccClass || cls == BS_UicClass )
            {
                lua_getfield(L,dep,"#decl");
                pushTargetName(L,lua_gettop(L));
                const int name = lua_gettop(L);
                lua_pushvalue(L,name);
                lua_rawget(L,visited);
                const int seen = !lua_isnil(L,-1);
                lua_pop(L,1);
                if( !seen )
                {
                    lua_pushvalue(L,name);
                    lua_pushboolean(L,1);
                    lua_rawset(L,visited);
                    if( out ) fprintf(out,"    \"%s\"\n", lua_tostring(L,name));
                    n++;
                }
                lua_pop(L,2); // decl, name
                n += addObjectDeps(L,dep,builtins,visited,out); // hoist nested object libs to the absorbing target
            }
            // real libraries/executables: stop, they are handled by addRealDeps
            lua_pop(L,1); // dep
        }
    }
    lua_pop(L,1); // deps

    assert( top == lua_gettop(L) );
    return n;
}

/* Collect real static/shared library (and executable) dependencies, linked PUBLIC so CMake propagates
 * their own transitive link requirements. We descend through groups and object libraries to reach real
 * libraries hidden behind them, but do not descend into real libraries (CMake handles lib->lib
 * transitivity). When out is NULL only counts. */
static int addRealDeps(lua_State* L, int inst, int builtins, FILE* out)
{
    const int top = lua_gettop(L);
    int n = 0;

    lua_getfield(L,inst,"deps");
    const int deps = lua_gettop(L);
    if( !lua_isnil(L,deps) )
    {
        size_t i;
        for( i = 1; i <= lua_objlen(L,deps); i++ )
        {
            lua_rawgeti(L,deps,i);
            const int dep = lua_gettop(L);
            const int cls = getClass(L,dep,builtins);
            if( cls == BS_GroupClass || cls == BS_SourceSetClass || cls == BS_MocClass ||
                    cls == BS_RccClass || cls == BS_UicClass )
                n += addRealDeps(L,dep,builtins,out); // look through object producers for real libs behind them
            else if( cls == BS_LibraryClass || cls == BS_ExecutableClass )
            {
                lua_getfield(L,dep,"#decl");
                pushTargetName(L,lua_gettop(L));
                if( out ) fprintf(out,"    \"%s\"\n", lua_tostring(L,-1));
                lua_pop(L,2); // decl, name
                n++;
            }
            lua_pop(L,1); // dep
        }
    }
    lua_pop(L,1); // deps

    assert( top == lua_gettop(L) );
    return n;
}

/* shared body: include dirs, defines, compile options and links for a compiled target.
 * each target_* command is only emitted when it would have at least one entry (an empty
 * target_link_libraries etc. is an error in CMake). isObjectLib is set for source sets, which - like
 * qmake - forward rather than absorb their deps, so they emit no link section at all (the absorbing
 * static/shared lib or executable links the whole flattened closure instead). */
static void addToolOrderDeps(lua_State* L, int inst, int builtins, const char* target, FILE* out);

static void genCommon(lua_State* L, int inst, int builtins, const char* target, FILE* out, int isObjectLib)
{
    if( addIncludes(L,inst,builtins,NULL) > 0 )
    {
        fprintf(out,"target_include_directories(%s PUBLIC\n", target);
        addIncludes(L,inst,builtins,out);
        fprintf(out,")\n");
    }

    if( addDefines(L,inst,NULL) > 0 )
    {
        fprintf(out,"target_compile_definitions(%s PUBLIC\n", target);
        addDefines(L,inst,out);
        fprintf(out,")\n");
    }

    if( addFlags(L,inst,NULL,"cflags","%s") + addFlags(L,inst,NULL,"cflags_c","%s")
            + addFlags(L,inst,NULL,"cflags_cc","%s") > 0 )
    {
        fprintf(out,"target_compile_options(%s PRIVATE\n", target);
        addFlags(L,inst,out,"cflags","%s");
        addFlags(L,inst,out,"cflags_c","$<$<COMPILE_LANGUAGE:C>:%s>");
        addFlags(L,inst,out,"cflags_cc","$<$<COMPILE_LANGUAGE:CXX>:%s>");
        fprintf(out,")\n");
    }

    if( !isObjectLib )
    {
        lua_newtable(L);
        const int visited = lua_gettop(L);
        const int objN = addObjectDeps(L,inst,builtins,visited,NULL);
        lua_pop(L,1); // visited (count pass)
        if( objN > 0 )
        {
            fprintf(out,"target_link_libraries(%s PRIVATE\n", target);
            lua_newtable(L);
            const int visited2 = lua_gettop(L);
            addObjectDeps(L,inst,builtins,visited2,out);
            lua_pop(L,1); // visited (emit pass)
            fprintf(out,")\n");
        }

        if( addRealDeps(L,inst,builtins,NULL) + addExtLibs(L,inst,builtins,NULL) > 0 )
        {
            fprintf(out,"target_link_libraries(%s PUBLIC\n", target);
            addRealDeps(L,inst,builtins,out);
            addExtLibs(L,inst,builtins,out);
            fprintf(out,")\n");
        }

        if( addFlags(L,inst,NULL,"ldflags","%s") > 0 )
        {
            fprintf(out,"target_link_options(%s PUBLIC\n", target);
            addFlags(L,inst,out,"ldflags","%s");
            fprintf(out,")\n");
        }
    }

    // order this target after any moc/rcc/uic generation it depends on, so #included generated
    // outputs (x.moc, ui_x.h) exist before this target's sources are compiled
    addToolOrderDeps(L,inst,builtins,target,out);
}

/* BUSY compiles moc/rcc/uic-generated sources as part of the *consumer* product, so their compilation
 * uses the consumer's include dirs and defines (bsqmakegen.c passes the moc include dir up the dep chain).
 * Since we model each tool product as its own OBJECT library, we push the consumer's include dirs and
 * defines onto those tool libraries here. Groups are flattened so their tool members are reached too.
 * Dependency-first emission order guarantees the tool targets already exist when we append to them. */
static void propagateToTools(lua_State* L, int inst, int builtins, int consumer, FILE* out)
{
    const int top = lua_gettop(L);
    lua_getfield(L,inst,"deps");
    const int deps = lua_gettop(L);
    if( !lua_isnil(L,deps) )
    {
        size_t i;
        for( i = 1; i <= lua_objlen(L,deps); i++ )
        {
            lua_rawgeti(L,deps,i);
            const int dep = lua_gettop(L);
            const int cls = getClass(L,dep,builtins);
            if( cls == BS_GroupClass )
                propagateToTools(L,dep,builtins,consumer,out);
            else if( cls == BS_MocClass || cls == BS_RccClass || cls == BS_UicClass )
            {
                lua_getfield(L,dep,"#decl");
                pushTargetName(L,lua_gettop(L));
                const int name = lua_gettop(L);
                if( addIncludes(L,consumer,builtins,NULL) > 0 )
                {
                    fprintf(out,"target_include_directories(%s PRIVATE\n", lua_tostring(L,name));
                    addIncludes(L,consumer,builtins,out);
                    fprintf(out,")\n");
                }
                if( addDefines(L,consumer,NULL) > 0 )
                {
                    fprintf(out,"target_compile_definitions(%s PRIVATE\n", lua_tostring(L,name));
                    addDefines(L,consumer,out);
                    fprintf(out,")\n");
                }
                lua_pop(L,2); // decl, name
            }
            lua_pop(L,1); // dep
        }
    }
    lua_pop(L,1); // deps
    assert( top == lua_gettop(L) );
}

static void pushLibType(lua_State* L, int inst, int isSourceSet, const char** kw)
{
    if( isSourceSet )
    {
        *kw = "OBJECT";
        return;
    }
    lua_getfield(L,inst,"lib_type");
    if( !lua_isnil(L,-1) && strcmp(lua_tostring(L,-1),"shared") == 0 )
        *kw = "SHARED";
    else
        *kw = "STATIC";
    lua_pop(L,1);
}

static void genLibrary(lua_State* L, int inst, int builtins, const char* target, FILE* out, int isSourceSet)
{
    const char* kw = "STATIC";
    pushLibType(L,inst,isSourceSet,&kw);

    fprintf(out,"add_library(%s %s\n", target, kw);
    const int n = addSources(L,inst,builtins,out);
    if( n == 0 )
        fprintf(out,"    \"${CMAKE_CURRENT_BINARY_DIR}/busy_empty.c\"\n");
    fprintf(out,")\n");

    genCommon(L,inst,builtins,target,out,isSourceSet);
    propagateToTools(L,inst,builtins,inst,out);
}

static void genExe(lua_State* L, int inst, int builtins, const char* target, FILE* out)
{
    fprintf(out,"add_executable(%s\n", target);
    const int n = addSources(L,inst,builtins,out);
    if( n == 0 )
        fprintf(out,"    \"${CMAKE_CURRENT_BINARY_DIR}/busy_empty.c\"\n");
    fprintf(out,")\n");

    genCommon(L,inst,builtins,target,out,0);

    // honor the BUSY '.name' field for the produced binary (the CMake target keeps its unique dotted
    // name; only the output file is renamed), matching the direct/Ninja/QMake backends
    lua_getfield(L,inst,"name");
    if( !lua_isnil(L,-1) && *lua_tostring(L,-1) != 0 )
        fprintf(out,"set_target_properties(%s PROPERTIES OUTPUT_NAME \"%s\")\n",
                target, lua_tostring(L,-1));
    lua_pop(L,1);

    propagateToTools(L,inst,builtins,inst,out);
}

/* Moc/Rcc/Uic: emit a custom command per source producing the generated file in the binary dir, then
 * an OBJECT library aggregating the generated .cpp files so dependents pull them in by linking the target.
 * Generated headers (x.moc, ui_x.h) land in the target's binary dir which is exposed as a PUBLIC include. */
typedef enum ToolKind { TOOL_MOC, TOOL_RCC, TOOL_UIC } ToolKind;

/* Each Qt tool is exposed as an (initially empty) cache variable that lets the user override the tool
 * binary (-DBUSY_MOC=/path/to/moc). When left empty, genTool defaults the tool to the project-built
 * tool copied by a Copy product (if any, see pushCopiedTool), otherwise to the plain tool name resolved
 * from PATH. The set() is emitted once per tool kind. */
static void ensureToolVar(lua_State* L, int builtins, const char* regField, const char* cmakeVar,
                          const char* toolName, FILE* out)
{
    lua_getfield(L,builtins,regField);
    const int declared = !lua_isnil(L,-1);
    lua_pop(L,1);
    if( declared )
        return;
    fprintf(out,"if(NOT DEFINED %s)\n", cmakeVar);
    fprintf(out,"    set(%s \"\" CACHE FILEPATH \"override path to the %s tool used by BUSY; "
                "empty uses the project-built tool if available, else '%s' from PATH\")\n",
            cmakeVar, toolName, toolName);
    fprintf(out,"endif()\n");
    lua_pushboolean(L,1);
    lua_setfield(L,builtins,regField);
}

/* push the tool product's generated-output directory as a relocatable CMake path, matching BUSY's
 * build_dir() (root_build_dir + module #rdir). This is the directory the consuming products add to
 * their include_dirs (via build_dir()), so #included outputs (x.moc, ui_x.h) are found on the include
 * path, and it is where the direct and ninja builds also place the generated files. */
static void pushToolOutDir(lua_State* L, int inst, int builtins)
{
    const int top = lua_gettop(L);
    lua_getfield(L,builtins,"#inst");
    const int binst = lua_gettop(L);
    lua_getfield(L,binst,"root_build_dir");
    const int bldRoot = lua_gettop(L);
    bs_getModuleVar(L,inst,"#rdir");
    addPath(L,bldRoot,lua_gettop(L));
    const int abs = lua_gettop(L);
    const size_t bldlen = strlen(lua_tostring(L,bldRoot));
    lua_pushfstring(L,"${CMAKE_CURRENT_BINARY_DIR}%s", lua_tostring(L,abs)+bldlen);
    lua_replace(L,binst); // move result down to the binst slot
    lua_pop(L,3); // bldRoot, #rdir, abs
    assert( lua_gettop(L) == top + 1 );
}

/* A consumer that #includes generated moc/uic output (e.g. a source set with .deps += run_moc) must be
 * built after the generation ran. Emit an explicit ordering dependency on each tool product's _gen
 * target found in the (group-flattened) direct deps. */
static void addToolOrderDeps(lua_State* L, int inst, int builtins, const char* target, FILE* out)
{
    const int top = lua_gettop(L);
    lua_getfield(L,inst,"deps");
    const int deps = lua_gettop(L);
    if( !lua_isnil(L,deps) )
    {
        size_t i;
        for( i = 1; i <= lua_objlen(L,deps); i++ )
        {
            lua_rawgeti(L,deps,i);
            const int dep = lua_gettop(L);
            const int cls = getClass(L,dep,builtins);
            if( cls == BS_GroupClass )
                addToolOrderDeps(L,dep,builtins,target,out);
            else if( cls == BS_MocClass || cls == BS_RccClass || cls == BS_UicClass )
            {
                lua_getfield(L,dep,"#decl");
                pushTargetName(L,lua_gettop(L));
                fprintf(out,"add_dependencies(%s %s_gen)\n", target, lua_tostring(L,-1));
                lua_pop(L,2); // decl, name
            }
            lua_pop(L,1); // dep
        }
    }
    lua_pop(L,1); // deps
    assert( top == lua_gettop(L) );
}

/* A tool product (Moc/Rcc/Uic) invokes its tool from a tool directory: the product's own tool_dir if
 * set, else the global <tool>_path builtin (moc_path/rcc_path/uic_path), exactly like the direct/Ninja
 * runner (bsvisitor.c runmoc/runrcc/runuic). The tool binary lives at <dir>/<toolName>. When a Copy
 * product places the project-built tool there (registered in #cmake_copyout by the pre-pass), push that
 * CMake path string and return 1 so genTool defaults to it and adds a build-ordering dependency on it.
 * Otherwise push nil and return 0 (the tool is then resolved from PATH / an override). */
static int pushCopiedTool(lua_State* L, int inst, int builtins, const char* toolName, const char* pathVar)
{
    const int top = lua_gettop(L);
    int have = 0;
    lua_getfield(L,inst,"tool_dir"); // +1 dir
    if( lua_isnil(L,-1) || strcmp(lua_tostring(L,-1),".") == 0 )
    {
        // no per-product tool_dir: fall back to the global <tool>_path builtin (a directory)
        lua_pop(L,1);
        lua_getfield(L,builtins,"#inst");
        lua_getfield(L,-1,pathVar);
        lua_replace(L,-2); // drop #inst, keep the path
    }
    const int dir = lua_gettop(L);
    if( !lua_isnil(L,dir) && strcmp(lua_tostring(L,dir),".") != 0 )
    {
        pushResolvedPath(L,inst,builtins,dir); // +1 resolved
        lua_pushfstring(L,"%s/%s", lua_tostring(L,-1), toolName); // +1 dest
        lua_getfield(L,builtins,"#cmake_copyout"); // +1 set
        if( !lua_isnil(L,-1) )
        {
            lua_pushvalue(L,-2); // dest key
            lua_rawget(L,-2);    // set[dest]
            have = !lua_isnil(L,-1);
            lua_pop(L,1); // lookup result
        }
        lua_pop(L,1); // set
        // stack: dir, resolved, dest
    }
    if( have )
    {
        lua_replace(L,top+1); // move dest into the dir slot (pops dest)
        lua_settop(L,top+1);  // drop resolved
    }else
    {
        lua_settop(L,top);
        lua_pushnil(L);
    }
    assert( lua_gettop(L) == top + 1 );
    return have;
}

static void genTool(lua_State* L, int inst, int builtins, const char* target, FILE* out, ToolKind kind)
{
    const char* toolName = kind == TOOL_MOC ? "moc" : kind == TOOL_RCC ? "rcc" : "uic";
    const char* regField = kind == TOOL_MOC ? "#cmake_BUSY_MOC" :
                           kind == TOOL_RCC ? "#cmake_BUSY_RCC" : "#cmake_BUSY_UIC";
    const char* toolVar = kind == TOOL_MOC ? "BUSY_MOC" : kind == TOOL_RCC ? "BUSY_RCC" : "BUSY_UIC";
    ensureToolVar(L,builtins,regField,toolVar,toolName,out);

    // if a Copy product places the project-built tool at tool_dir/<toolName>, default to it (and add a
    // build-ordering dependency on it below); the user can still override via -D<toolVar>=<path>.
    const char* pathVar = kind == TOOL_MOC ? "moc_path" : kind == TOOL_RCC ? "rcc_path" : "uic_path";
    const int haveCopiedTool = pushCopiedTool(L,inst,builtins,toolName,pathVar);
    const int copiedPath = lua_gettop(L); // string (copied tool path) or nil
    fprintf(out,"set(%s_TOOL \"%s\")\n", target,
            haveCopiedTool ? lua_tostring(L,copiedPath) : toolName);
    fprintf(out,"if(%s)\n    set(%s_TOOL \"${%s}\")\nendif()\n", toolVar, target, toolVar);
    lua_pushfstring(L,"${%s_TOOL}",target);
    const int tool = lua_gettop(L);

    // generated files go into the module build_dir() (root_build_dir + #rdir), the same directory the
    // consuming products add to their include_dirs, so #included outputs (x.moc, ui_x.h) are found.
    pushToolOutDir(L,inst,builtins);
    const int outdir = lua_gettop(L);

    fprintf(out,"set(%s_GENSRC)\n", target);
    fprintf(out,"set(%s_ALL)\n", target);
    fprintf(out,"file(MAKE_DIRECTORY \"%s\")\n", lua_tostring(L,outdir));

    lua_getfield(L,inst,"sources");
    const int sources = lua_gettop(L);
    size_t i;
    for( i = 1; i <= lua_objlen(L,sources); i++ )
    {
        lua_rawgeti(L,sources,i);
        const int src = lua_gettop(L);
        pushResolvedPath(L,inst,builtins,src);
        const int inpath = lua_gettop(L);

        int blen;
        const char* base = bs_path_part(lua_tostring(L,src),BS_baseName,&blen);
        lua_pushlstring(L,base,blen);
        const int basename = lua_gettop(L);

        int elen;
        const char* ext = bs_path_part(lua_tostring(L,src),BS_extension,&elen);
        const int isHeader = ( elen == 0 ) || ( bs_guessLang(lua_tostring(L,src)) == BS_header );

        // <t>_GENSRC collects outputs that are compiled into the object library (moc_x.cpp, qrc_x.cpp);
        // <t>_ALL collects every generated file so a helper target can force generation before consumers
        // compile. Headers produced by moc (x.moc) and uic (ui_x.h) are #included, never compiled.
        if( kind == TOOL_MOC )
        {
            const char* pattern = isHeader ? "moc_%s.cpp" : "%s.moc";
            char outfile[512];
            sprintf(outfile,pattern,lua_tostring(L,basename));
            fprintf(out,"add_custom_command(OUTPUT \"%s/%s\"\n", lua_tostring(L,outdir), outfile);
            fprintf(out,"    COMMAND \"%s\" \"%s\" -o \"%s/%s\"",
                    lua_tostring(L,tool), lua_tostring(L,inpath), lua_tostring(L,outdir), outfile);
            // pass the moc product's own defines to moc so it evaluates the same #ifdefs BUSY does when
            // parsing the input (e.g. QT_NO_GESTURES prunes gesture enums); matches bsrunner.c runmoc.
            {
                lua_getfield(L,inst,"defines");
                const int mdefs = lua_gettop(L);
                size_t k;
                for( k = 1; k <= lua_objlen(L,mdefs); k++ )
                {
                    lua_rawgeti(L,mdefs,k);
                    fprintf(out," -D \"%s\"", lua_tostring(L,-1));
                    lua_pop(L,1);
                }
                lua_pop(L,1); // defines
            }
            // BUSY auto-includes a sibling <name>_p.h private header in the moc output when present, so the
            // generated meta-object code sees the complete private class (bsrunner.c runmoc). Replicate it:
            // -p sets the include path prefix, -b forces the #include. Only for header inputs, matching BUSY.
            if( isHeader )
            {
                // real path of the source to test for the sibling _p.h on disk
                if( *lua_tostring(L,src) == '/' )
                    lua_pushvalue(L,src);
                else
                {
                    bs_getModuleVar(L,inst,"#dir");
                    addPath(L,lua_gettop(L),src);
                    lua_remove(L,-2);
                }
                const int abs = lua_gettop(L);
                lua_pushstring(L,"{{source_dir}}/{{source_name_part}}_p.h");
                bs_apply_source_expansion(lua_tostring(L,abs),lua_tostring(L,-1),0);
                if( bs_exists2(bs_global_buffer()) )
                {
                    // include-path prefix = directory part of the (relocatable) CMake input path
                    const char* ip = lua_tostring(L,inpath);
                    const char* slash = strrchr(ip,'/');
                    const int dlen = slash ? (int)(slash - ip) : 0;
                    fprintf(out," -p \"%.*s\" -b \"%s_p.h\"", dlen, ip, lua_tostring(L,basename));
                }
                lua_pop(L,2); // template, abs
            }
            fprintf(out,"\n");
            if( haveCopiedTool )
                fprintf(out,"    DEPENDS \"%s\" \"%s\" VERBATIM)\n",
                        lua_tostring(L,inpath), lua_tostring(L,copiedPath));
            else
                fprintf(out,"    DEPENDS \"%s\" VERBATIM)\n", lua_tostring(L,inpath));
            fprintf(out,"list(APPEND %s_ALL \"%s/%s\")\n", target, lua_tostring(L,outdir), outfile);
            if( isHeader )
                fprintf(out,"list(APPEND %s_GENSRC \"%s/%s\")\n", target, lua_tostring(L,outdir), outfile);
        }else if( kind == TOOL_RCC )
        {
            fprintf(out,"add_custom_command(OUTPUT \"%s/qrc_%s.cpp\"\n",
                    lua_tostring(L,outdir), lua_tostring(L,basename));
            fprintf(out,"    COMMAND \"%s\" \"%s\" -o \"%s/qrc_%s.cpp\" -name \"%s\"\n",
                    lua_tostring(L,tool), lua_tostring(L,inpath), lua_tostring(L,outdir), lua_tostring(L,basename),
                    lua_tostring(L,basename));
            if( haveCopiedTool )
                fprintf(out,"    DEPENDS \"%s\" \"%s\" VERBATIM)\n",
                        lua_tostring(L,inpath), lua_tostring(L,copiedPath));
            else
                fprintf(out,"    DEPENDS \"%s\" VERBATIM)\n", lua_tostring(L,inpath));
            fprintf(out,"list(APPEND %s_ALL \"%s/qrc_%s.cpp\")\n",
                    target, lua_tostring(L,outdir), lua_tostring(L,basename));
            fprintf(out,"list(APPEND %s_GENSRC \"%s/qrc_%s.cpp\")\n",
                    target, lua_tostring(L,outdir), lua_tostring(L,basename));
        }else // TOOL_UIC
        {
            fprintf(out,"add_custom_command(OUTPUT \"%s/ui_%s.h\"\n",
                    lua_tostring(L,outdir), lua_tostring(L,basename));
            fprintf(out,"    COMMAND \"%s\" \"%s\" -o \"%s/ui_%s.h\"\n",
                    lua_tostring(L,tool), lua_tostring(L,inpath), lua_tostring(L,outdir), lua_tostring(L,basename));
            if( haveCopiedTool )
                fprintf(out,"    DEPENDS \"%s\" \"%s\" VERBATIM)\n",
                        lua_tostring(L,inpath), lua_tostring(L,copiedPath));
            else
                fprintf(out,"    DEPENDS \"%s\" VERBATIM)\n", lua_tostring(L,inpath));
            fprintf(out,"list(APPEND %s_ALL \"%s/ui_%s.h\")\n",
                    target, lua_tostring(L,outdir), lua_tostring(L,basename));
        }

        lua_pop(L,3); // src, inpath, basename
    }
    lua_pop(L,1); // sources

    // <t>_gen forces all outputs to be produced; the OBJECT library depends on it, so any product that
    // links this tool product (a) compiles the compiled outputs and (b) is ordered after all generated
    // headers exist, and (c) inherits the output directory as a PUBLIC include for #included headers.
    fprintf(out,"add_custom_target(%s_gen DEPENDS ${%s_ALL})\n", target, target);
    fprintf(out,"add_library(%s OBJECT ${%s_GENSRC} \"${CMAKE_CURRENT_BINARY_DIR}/busy_empty.c\")\n",
            target, target);
    fprintf(out,"add_dependencies(%s %s_gen)\n", target, target);
    // the tool product carries the include_dirs and defines needed to compile the generated sources
    // (BUSY populates them from the product's configs); emit the tool's own output dir as PUBLIC so
    // #included headers (x.moc, ui_x.h) reach consumers, and the rest as PRIVATE build requirements.
    fprintf(out,"target_include_directories(%s PUBLIC \"%s\")\n",
            target, lua_tostring(L,outdir));
    if( addIncludes(L,inst,builtins,NULL) > 0 )
    {
        fprintf(out,"target_include_directories(%s PRIVATE\n", target);
        addIncludes(L,inst,builtins,out);
        fprintf(out,")\n");
    }
    if( addDefines(L,inst,NULL) > 0 )
    {
        fprintf(out,"target_compile_definitions(%s PRIVATE\n", target);
        addDefines(L,inst,out);
        fprintf(out,")\n");
    }
    fprintf(out,"\n");

    lua_pop(L,3); // outdir, tool, copiedPath
}

/* a Group is an aggregate with no output of its own; model it as an INTERFACE library that
 * link-forwards its member products, so linking the group into a target pulls in the members'
 * objects and usage requirements transitively (matches BUSY's group semantics) */
static void genGroup(lua_State* L, int inst, int builtins, const char* target, FILE* out)
{
    fprintf(out,"add_library(%s INTERFACE)\n", target);

    lua_newtable(L);
    const int visited = lua_gettop(L);
    const int objN = addObjectDeps(L,inst,builtins,visited,NULL);
    lua_pop(L,1);
    const int realN = addRealDeps(L,inst,builtins,NULL) + addExtLibs(L,inst,builtins,NULL);
    if( objN + realN > 0 )
    {
        fprintf(out,"target_link_libraries(%s INTERFACE\n", target);
        lua_newtable(L);
        const int visited2 = lua_gettop(L);
        addObjectDeps(L,inst,builtins,visited2,out);
        lua_pop(L,1);
        addRealDeps(L,inst,builtins,out);
        addExtLibs(L,inst,builtins,out);
        fprintf(out,")\n");
    }
}

/* does the Copy product's use_deps request dependencies of the given product class? */
static int copyWantsDep(lua_State* L, int copyInst, int depCls)
{
    int want = 0;
    lua_getfield(L,copyInst,"use_deps");
    const int ud = lua_gettop(L);
    if( !lua_isnil(L,ud) )
    {
        size_t i;
        for( i = 1; i <= lua_objlen(L,ud); i++ )
        {
            lua_rawgeti(L,ud,i);
            const char* k = lua_tostring(L,-1);
            if( depCls == BS_ExecutableClass && strcmp(k,"executable") == 0 )
                want = 1;
            else if( depCls == BS_LibraryClass && (strcmp(k,"static_lib")==0 || strcmp(k,"shared_lib")==0) )
                want = 1;
            else if( depCls == BS_SourceSetClass && strcmp(k,"object_file")==0 )
                want = 1;
            lua_pop(L,1);
        }
    }
    lua_pop(L,1); // use_deps
    return want;
}

/* Translate a Copy product. For each matching dependency (filtered by .use_deps) and each .outputs
 * pattern, the destination is the source-expanded output resolved under root_build_dir
 * (${CMAKE_CURRENT_BINARY_DIR}/...), matching BUSY. When out != NULL, emit an add_custom_command that
 * copies the built dependency artifact ($<TARGET_FILE:...>) to the destination and an aggregating
 * custom target; the copy is portable and needs no external tool (${CMAKE_COMMAND} -E copy_if_different).
 * The destinations are always registered in builtins.#cmake_copyout so tool products (moc/rcc/uic) can
 * discover the copied tool at tool_dir/<toolName> and depend on it (see pushCopiedTool). */
static void doCopy(lua_State* L, int inst, int builtins, const char* target, FILE* out)
{
    const int top = lua_gettop(L);

    lua_getfield(L,builtins,"#cmake_copyout");
    if( lua_isnil(L,-1) )
    {
        lua_pop(L,1);
        lua_newtable(L);
        lua_pushvalue(L,-1);
        lua_setfield(L,builtins,"#cmake_copyout");
    }
    const int set = lua_gettop(L);

    if( out )
        fprintf(out,"set(%s_ALL)\n", target);

    lua_getfield(L,inst,"deps");
    const int deps = lua_gettop(L);
    lua_getfield(L,inst,"outputs");
    const int outputs = lua_gettop(L);

    if( !lua_isnil(L,deps) && !lua_isnil(L,outputs) )
    {
        size_t d;
        for( d = 1; d <= lua_objlen(L,deps); d++ )
        {
            lua_rawgeti(L,deps,d);
            const int dep = lua_gettop(L);
            if( copyWantsDep(L,inst,getClass(L,dep,builtins)) )
            {
                lua_getfield(L,dep,"#decl");
                pushTargetName(L,lua_gettop(L));
                const int depTarget = lua_gettop(L); // string

                // BUSY expands {{source_file_part}} etc. against the dependency's output file; give the
                // expansion a normalized path (leading "./") so bs_path_part yields the file name
                lua_getfield(L,dep,"name");
                const char* rawName = lua_tostring(L,-1);
                if( rawName == NULL )
                {
                    const char* tn = lua_tostring(L,depTarget);
                    const char* dot = strrchr(tn,'.');
                    rawName = dot ? dot+1 : tn;
                }
                lua_pushfstring(L,"./%s",rawName);
                const int depSrc = lua_gettop(L); // normalized "source" for expansion

                lua_getfield(L,builtins,"#inst");
                lua_getfield(L,-1,"root_build_dir");
                const int bldRoot = lua_gettop(L);
                const size_t bldlen = strlen(lua_tostring(L,bldRoot));

                size_t o;
                for( o = 1; o <= lua_objlen(L,outputs); o++ )
                {
                    lua_rawgeti(L,outputs,o);
                    if( bs_apply_source_expansion(lua_tostring(L,depSrc),lua_tostring(L,-1),0) != BS_OK )
                        luaL_error(L,"invalid placeholders in Copy 'outputs': %s", lua_tostring(L,-1));
                    // resolve the (root_build_dir-relative) output the same way pushResolvedPath does for
                    // tool_dir, so a copied tool's path matches tool_dir/<toolName> exactly (no ./ vs / drift)
                    lua_pushstring(L,bs_global_buffer());
                    addPath(L,bldRoot,lua_gettop(L));
                    const int abs = lua_gettop(L);
                    lua_pushfstring(L,"${CMAKE_CURRENT_BINARY_DIR}%s", lua_tostring(L,abs)+bldlen);
                    const int dest = lua_gettop(L);

                    lua_pushvalue(L,dest);
                    lua_pushvalue(L,depTarget);
                    lua_rawset(L,set); // #cmake_copyout[dest] = depTarget

                    if( out )
                    {
                        const char* ds = lua_tostring(L,dest);
                        const char* slash = strrchr(ds,'/');
                        if( slash )
                            fprintf(out,"file(MAKE_DIRECTORY \"%.*s\")\n", (int)(slash-ds), ds);
                        fprintf(out,"add_custom_command(OUTPUT \"%s\"\n", ds);
                        fprintf(out,"    COMMAND \"${CMAKE_COMMAND}\" -E copy_if_different "
                                    "\"$<TARGET_FILE:%s>\" \"%s\"\n", lua_tostring(L,depTarget), ds);
                        // depend on the target's output file (not its name): with OUTPUT_NAME the file
                        // differs from the target name, and $<TARGET_FILE:> is both a file and target dep
                        fprintf(out,"    DEPENDS \"$<TARGET_FILE:%s>\" VERBATIM)\n", lua_tostring(L,depTarget));
                        fprintf(out,"list(APPEND %s_ALL \"%s\")\n", target, ds);
                    }
                    lua_pop(L,3); // dest, abs, relative-expanded, ... (dest, abs, expanded)
                    lua_pop(L,1); // output pattern
                }
                lua_pop(L,2); // bldRoot, binst
                lua_pop(L,2); // depSrc, name
                lua_pop(L,1); // depTarget (+ decl below)
                lua_pop(L,1); // decl
            }
            lua_pop(L,1); // dep
        }
    }

    if( out )
        fprintf(out,"add_custom_target(%s DEPENDS ${%s_ALL})\n", target, target);

    lua_pop(L,3); // outputs, deps, set
    assert( top == lua_gettop(L) );
}

static int genproduct(lua_State* L) // args: prodinst, out(lightuserdata)
{
    const int prodinst = 1;
    const int top = lua_gettop(L);

    FILE* out = (FILE*)lua_touserdata(L,2);

    lua_getglobal(L, "require");
    lua_pushstring(L, "builtins");
    lua_call(L,1,1);
    const int builtins = lua_gettop(L);

    lua_getfield(L,prodinst,"#decl");
    const int decl = lua_gettop(L);
    pushTargetName(L,decl);
    const int target = lua_gettop(L);

    lua_getfield(L,builtins,"#cmake_project");
    const int proj = lua_gettop(L);

    const int cls = getClass(L,prodinst,builtins);

    fprintf(out,"# %s\n", lua_tostring(L,target));

    switch( cls )
    {
    case BS_LibraryClass:
        genLibrary(L,prodinst,builtins,lua_tostring(L,target),out,0);
        fprintf(out,"add_library(%s::%s ALIAS %s)\n",
                lua_tostring(L,proj), lua_tostring(L,target), lua_tostring(L,target));
        break;
    case BS_ExecutableClass:
        genExe(L,prodinst,builtins,lua_tostring(L,target),out);
        break;
    case BS_SourceSetClass:
        genLibrary(L,prodinst,builtins,lua_tostring(L,target),out,1);
        fprintf(out,"add_library(%s::%s ALIAS %s)\n",
                lua_tostring(L,proj), lua_tostring(L,target), lua_tostring(L,target));
        break;
    case BS_MocClass:
        genTool(L,prodinst,builtins,lua_tostring(L,target),out,TOOL_MOC);
        break;
    case BS_RccClass:
        genTool(L,prodinst,builtins,lua_tostring(L,target),out,TOOL_RCC);
        break;
    case BS_UicClass:
        genTool(L,prodinst,builtins,lua_tostring(L,target),out,TOOL_UIC);
        break;
    case BS_GroupClass:
        genGroup(L,prodinst,builtins,lua_tostring(L,target),out);
        fprintf(out,"add_library(%s::%s ALIAS %s)\n",
                lua_tostring(L,proj), lua_tostring(L,target), lua_tostring(L,target));
        break;
    case BS_CopyClass:
        doCopy(L,prodinst,builtins,lua_tostring(L,target),out);
        break;
    default:
        fprintf(out,"# class %s not supported by the cmake generator\n", getClassName(cls));
        break;
    }

    fprintf(out,"\n");

    lua_pop(L,4); // builtins, decl, target, proj
    assert( top == lua_gettop(L) );
    return 0;
}

int bs_genCmake(lua_State* L) // args: root module def, array of productinst
{
    enum { ROOT = 1, PRODS };
    const int top = lua_gettop(L);
    size_t i;

    lua_createtable(L,0,0);
    const int order = lua_gettop(L);
    for( i = 1; i <= lua_objlen(L,PRODS); i++ )
    {
        lua_pushcfunction(L,mark);
        lua_rawgeti(L,PRODS,i);
        lua_pushvalue(L,order);
        lua_call(L,2,0);
    }

    lua_getglobal(L, "require");
    lua_pushstring(L, "builtins");
    lua_call(L,1,1);
    const int builtins = lua_gettop(L);

    lua_getfield(L,builtins,"#inst");
    const int binst = lua_gettop(L);

    lua_getfield(L,binst,"root_source_dir");
    const int sourceDir = lua_gettop(L);

    lua_pushfstring(L,"%s/CMakeLists.txt", lua_tostring(L,sourceDir));
    const int listsPath = lua_gettop(L);

    if( bs_exists(lua_tostring(L,listsPath)) )
        luaL_error(L,"a CMakeLists.txt already exists at %s; remove it before generating, "
                     "or use -B to generate into a different directory",
                   bs_denormalize_path(lua_tostring(L,listsPath)));

    fprintf(stdout,"# generating %s\n", bs_denormalize_path(lua_tostring(L,listsPath)));
    fflush(stdout);

    FILE* out = bs_fopen(bs_denormalize_path(lua_tostring(L,listsPath)),"w");
    if( out == NULL )
        luaL_error(L,"cannot open file for writing: %s", lua_tostring(L,listsPath));

    int nlen;
    const char* pname = bs_path_part(lua_tostring(L,sourceDir),BS_fileName,&nlen);
    if( nlen > 0 )
        lua_pushlstring(L,pname,nlen);
    else
        lua_pushstring(L,"BusyProject");
    lua_setfield(L,builtins,"#cmake_project"); // used by genproduct for namespaced ALIAS targets

    fprintf(out,"# generated by BUSY, do not modify\n");
    fprintf(out,"cmake_minimum_required(VERSION 3.13)\n");
    lua_getfield(L,builtins,"#cmake_project");
    fprintf(out,"project(%s C CXX)\n\n", lua_tostring(L,-1));
    lua_pop(L,1);

    fprintf(out,"file(WRITE \"${CMAKE_CURRENT_BINARY_DIR}/busy_empty.c\" \"\")\n\n");

    // emit BUSY's build-mode toolchain defaults (e.g. -O2 for the default 'optimized' mode) globally --
    // the same defaults the direct/Ninja backends prepend to every compile/link. Without these CMake
    // would compile at -O0 and produce a larger, slower binary.
    lua_getfield(L,binst,"#ctdefaults");
    lua_getfield(L,binst,"target_toolchain");
    lua_rawget(L,-2);
    const int ctd = lua_gettop(L);
    if( !lua_isnil(L,ctd) )
    {
        if( addFlags(L,ctd,NULL,"cflags","%s") + addFlags(L,ctd,NULL,"cflags_c","%s")
                + addFlags(L,ctd,NULL,"cflags_cc","%s") > 0 )
        {
            fprintf(out,"add_compile_options(\n");
            addFlags(L,ctd,out,"cflags","%s");
            addFlags(L,ctd,out,"cflags_c","$<$<COMPILE_LANGUAGE:C>:%s>");
            addFlags(L,ctd,out,"cflags_cc","$<$<COMPILE_LANGUAGE:CXX>:%s>");
            fprintf(out,")\n");
        }
        if( addFlags(L,ctd,NULL,"ldflags","%s") > 0 )
        {
            fprintf(out,"add_link_options(\n");
            addFlags(L,ctd,out,"ldflags","%s");
            fprintf(out,")\n");
        }
        fprintf(out,"\n");
    }
    lua_pop(L,2); // ctd, #ctdefaults

    const size_t len = lua_objlen(L,order);

    // pre-pass: register every Copy product's destination(s) in #cmake_copyout, so tool products
    // (moc/rcc/uic) emitted before their Copy can still discover the copied tool at tool_dir/<toolName>
    for( i = 1; i <= len; i++ )
    {
        lua_rawgeti(L,order,i);
        const int decl = lua_gettop(L);
        lua_getfield(L,decl,"#owner");
        lua_getfield(L,-1,"#inst");
        lua_replace(L,-2);
        lua_getfield(L,decl,"#name");
        lua_rawget(L,-2);
        lua_replace(L,-2);
        const int prodinst = lua_gettop(L);
        if( getClass(L,prodinst,builtins) == BS_CopyClass )
            doCopy(L,prodinst,builtins,NULL,NULL);
        lua_pop(L,2); // decl, prodinst
    }

    for( i = 1; i <= len; i++ )
    {
        lua_rawgeti(L,order,i);
        const int decl = lua_gettop(L);

        // resolve the product instance from decl.#owner.#inst[decl.#name]
        lua_getfield(L,decl,"#owner");
        lua_getfield(L,-1,"#inst");
        lua_replace(L,-2);
        lua_getfield(L,decl,"#name");
        lua_rawget(L,-2);
        lua_replace(L,-2);
        const int prodinst = lua_gettop(L);

        const int cls = getClass(L,prodinst,builtins);
        if( cls == BS_LibraryClass || cls == BS_ExecutableClass || cls == BS_SourceSetClass ||
                cls == BS_MocClass || cls == BS_RccClass || cls == BS_UicClass || cls == BS_GroupClass ||
                cls == BS_CopyClass )
        {
            lua_getfield(L,decl,"#cmake");
            fprintf(stdout,"# generating %s\n", lua_tostring(L,-1));
            fflush(stdout);
            lua_pop(L,1);

            lua_pushcfunction(L,genproduct);
            lua_pushvalue(L,prodinst);
            lua_pushlightuserdata(L,out);
            lua_call(L,2,0);
        }else if( cls != BS_ConfigClass )
        {
            lua_getfield(L,decl,"#cmake");
            fprintf(stdout,"# not generating \"%s\" because class \"%s\" is not supported by the cmake generator\n",
                    lua_tostring(L,-1), getClassName(cls));
            fflush(stdout);
            lua_pop(L,1);
        }

        lua_pop(L,2); // decl, prodinst
    }

    fclose(out);

    lua_pop(L,5); // order, builtins, binst, sourceDir, listsPath
    assert( top == lua_gettop(L) );
    return 0;
}
