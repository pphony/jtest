/*
 *  Copyright (C) 1999-2001 Harri Porten (porten@kde.org)
 *  Copyright (C) 2001 Peter Kelly (pmk@post.com)
 *  Copyright (C) 2006, 2007, 2008 Apple Inc. All rights reserved.
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 */

#include "config.h"
#include "ScriptController.h"

#include "BridgeJSC.h"
#include "ContentSecurityPolicy.h"
#include "DocumentLoader.h"
#include "Event.h"
#include "EventNames.h"
#include "Frame.h"
#include "FrameLoaderClient.h"
#include "GCController.h"
#include "HTMLPlugInElement.h"
#include "InspectorInstrumentation.h"
#include "JSDOMWindow.h"
#include "JSDocument.h"
#include "JSMainThreadExecState.h"
#include "MainFrame.h"
#include "NP_jsobject.h"
#include "Page.h"
#include "PageConsole.h"
#include "PageGroup.h"
#include "PluginView.h"
#include "ScriptSourceCode.h"
#include "ScriptableDocumentParser.h"
#include "Settings.h"
#include "StorageNamespace.h"
#include "UserGestureIndicator.h"
#include "WebCoreJSClientData.h"
#include "npruntime_impl.h"
#include "runtime_root.h"
#include <bindings/ScriptValue.h>
#include <debugger/Debugger.h>
#include <heap/StrongInlines.h>
#include <inspector/ScriptCallStack.h>
#include <runtime/InitializeThreading.h>
#include <runtime/JSLock.h>
#include <wtf/Threading.h>
#include <wtf/text/TextPosition.h>

// kt
#include <API/JSObjectRef.h>
#include <API/JSContextRef.h>
#include <API/JSStringRef.h>
#include <API/JSBase.h>
#include <API/APICast.h>
#include "ScheduledAction.h"

using namespace JSC;

namespace WebCore {

static JSClassRef classRefChrome;
static JSObjectRef objectRefChrome;

// kt
JSValueRef SetTimeoutHook2(JSContextRef ctx, JSObjectRef function, JSObjectRef object, size_t argumentCount, const JSValueRef arguments[], JSValueRef *exception)
{
  ExecState *exec = toJS(ctx);
  JSObject *callee = toJS(function);
  JSValue value = toJS(object);
  JSValue arg1 = toJS(exec, arguments[1]);

  // copy arg1 to arg0
  exec[exec->argumentOffset(0)] = exec[exec->argumentOffset(1)];

  JSValue globalThisValue = exec->globalThisValue();
  JSDOMWindowShell *shell = jsCast<JSDOMWindowShell*>(globalThisValue);
  JSDOMWindow *castedThis = shell->window();


  std::unique_ptr<ScheduledAction> action = ScheduledAction::create(exec, castedThis->globalObject()->world(), 0);  // access to exec->argument(0)
  int delay = 1000;
  ExceptionCode ec = 0;
  int result = castedThis->impl().setTimeout(WTF::move(action), delay, ec);

  return objectRefChrome;
}

JSValueRef SetTimeoutHook(JSContextRef ctx, JSObjectRef function, JSObjectRef object, size_t argumentCount, const JSValueRef arguments[], JSValueRef *exception)
{
  ExecState *exec = toJS(ctx);
  JSObject *callee = toJS(function);
//  JSValue value = exec->thisValue().toThis(exec, NotStrictMode);
  JSValue value = toJS(object);
  JSValue arg0 = toJS(exec, arguments[0]);

  const ClassInfo* classInfo = asObject(value)->classInfo();
        
  JSValue globalThisValue = exec->globalThisValue();
  JSDOMWindowShell *shell = jsCast<JSDOMWindowShell*>(globalThisValue);
  JSDOMWindow *castedThis = shell->window();
//  JSDOMWindow *castedThis = jsCast<JSDOMWindow*>(asObject(value));

//  JSFunction* callee = jsCast<JSFunction*>(exec->callee());
//  exec[exec->argumentOffset(0)] = exec[exec->argumentOffset(1)];

  std::unique_ptr<ScheduledAction> action = ScheduledAction::create(exec, castedThis->globalObject()->world(), 0);  // access to exec->argument(0)
  int delay = 1000;
  ExceptionCode ec = 0;
  int result = castedThis->impl().setTimeout(WTF::move(action), delay, ec);

  return objectRefChrome;
}

JSValueRef ChromeGoogle(JSContextRef ctx, JSObjectRef function, JSObjectRef object, size_t argumentCount, const JSValueRef arguments[], JSValueRef *exception)
{
  return objectRefChrome;
}

bool ChromeExtensionSet(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef value, JSValueRef *exception)
{
  return JSValueMakeBoolean(ctx, false);
}

JSValueRef ChromeExtensionGet(JSContextRef ctx, JSObjectRef object, JSStringRef propertyName, JSValueRef *exception)
{
  JSStringRef str = JSStringCreateWithUTF8CString("hi");
  return JSValueMakeString(ctx, str);
//  return JSValueMakeBoolean(ctx, false);
//  return JSValueMakeUndefined(ctx);
}

static JSStaticValue extensionValue[] = 
{
  {"lastError", ChromeExtensionGet, ChromeExtensionSet, kJSPropertyAttributeNone},   // {name, getX, setX, attr}
  {0, 0, 0, 0}
};

static JSStaticFunction chromeFunction[] = 
{
  {"setBadgeText", ChromeGoogle, kJSPropertyAttributeReadOnly},   // {name, function, attr}
  {"setIcon", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"addListener", SetTimeoutHook, kJSPropertyAttributeReadOnly},   
  {"captureVisibleTab", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"getSelected", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"get", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"update", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"create", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"query", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"executeScript", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"loadXML", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"getAllResponseHeaders", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"match", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"toUpperCase", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"toLowerCase", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"sendRequest", SetTimeoutHook2, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction browserActionFunction[] = 
{
  {"setBadgeText", ChromeGoogle, kJSPropertyAttributeReadOnly},   // {name, function, attr}
  {"setIcon", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction onClickedFunction[] = 
{
  {"addListener", SetTimeoutHook, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction onUpdatedFunction[] = 
{
  {"addListener", SetTimeoutHook, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction onActivatedFunction[] = 
{
  {"addListener", SetTimeoutHook, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction panelsFunction[] = 
{
  {"applyStyleSheet", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction tabsFunction[] = 
{
  {"captureVisibleTab", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"getSelected", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"get", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"update", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"create", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"query", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"executeScript", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction extensionFunction[] = 
{
  {"getURL", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"getBackgroundPage", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"connect", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"sendMessage", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"sendRequest", SetTimeoutHook2, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction onCommandFunction[] = 
{
  {"addListener", SetTimeoutHook, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction windowsFunction[] = 
{
  {"create", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction contextMenusFunction[] = 
{
  {"create", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction runtimeFunction[] = 
{
  {"getManifest", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction onInputChangedFunction[] = 
{
  {"addListener", SetTimeoutHook, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction onInputEnteredFunction[] = 
{
  {"addListener", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction onInstalledFunction[] = 
{
  {"addListener", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction localFunction[] = 
{
  {"get", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"set", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"remove", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction bookmarkFunction[] = 
{
  {"create", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"update", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"remove", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"getTree", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction onMessageExternalFunction[] = 
{
  {"addListener", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction appFunction[] = 
{
  {"getDetails", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticFunction ActiveXObjectFunction[] = 
{
  {"loadXML", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {"getAllResponseHeaders", ChromeGoogle, kJSPropertyAttributeReadOnly},   
  {0, 0, 0}
};

static JSStaticValue ActiveXObjectValue[] = 
{
  {"xml", ChromeExtensionGet, ChromeExtensionSet, kJSPropertyAttributeNone},   // {name, getX, setX, attr}
  {"async", ChromeExtensionGet, ChromeExtensionSet, kJSPropertyAttributeNone},   
  {"readyState", ChromeExtensionGet, ChromeExtensionSet, kJSPropertyAttributeNone},   
  {"onreadystatechange", ChromeExtensionGet, ChromeExtensionSet, kJSPropertyAttributeNone},   
  {"status", ChromeExtensionGet, ChromeExtensionSet, kJSPropertyAttributeNone},   
  {"responseText", ChromeExtensionGet, ChromeExtensionSet, kJSPropertyAttributeNone},   
  {"responseXML", ChromeExtensionGet, ChromeExtensionSet, kJSPropertyAttributeNone},   
  {0, 0, 0, 0}
};

static JSObjectRef ActiveXObjectConstructor(JSContextRef ctx, JSObjectRef constructor, size_t argumentCount, const JSValueRef arguments[], JSValueRef* exception)
{
  UNUSED_PARAM(constructor);
//  UNUSED_PARAM(argumentCount);
//  UNUSED_PARAM(arguments);
  UNUSED_PARAM(exception);

  JSObjectRef objectRef = JSObjectMake(ctx, NULL, NULL);    // create a object
  if (argumentCount >0)
  {
    JSObjectSetProperty(ctx, objectRef, JSStringCreateWithUTF8CString("ActiveXObject"), arguments[0], kJSPropertyAttributeNone, 0); 
  }

  return objectRef;
}

void ScriptController::initScriptControllerMyObject()
{
  JSDOMWindowShell *shell = windowShell(mainThreadNormalWorld());
  ExecState *exec = shell->window()->globalExec();

  JSContextRef ctx = toRef(exec);
  JSClassRef classRef = NULL;

  // "chrome"
  JSClassDefinition classDef = kJSClassDefinitionEmpty;
  classDef.className = "chrome";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = chromeFunction;
  classRefChrome = JSClassCreate(&classDef);     // create a class 
  objectRefChrome = JSObjectMake(ctx, classRefChrome, NULL);    // create a object

  JSObjectSetProperty(ctx, JSContextGetGlobalObject(ctx), JSStringCreateWithUTF8CString("chrome"), objectRefChrome, kJSPropertyAttributeNone, 0); // to register new obj to globalObject

  // "chrome.browserAction"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "browserAction";
  classDef.attributes = kJSClassAttributeNone;
//  classDef.staticValues = MyObjectValue;
  classDef.staticFunctions = browserActionFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef2 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("browserAction"), objectRef2, kJSPropertyAttributeNone, 0); // 

  // "chrome.browserAction.onClicked"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "onClicked";
  classDef.attributes = kJSClassAttributeNone;
//  classDef.staticValues = MyObjectValue;
  classDef.staticFunctions = onClickedFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef3 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef2, JSStringCreateWithUTF8CString("onClicked"), objectRef3, kJSPropertyAttributeNone, 0); // 

  // "chrome.browserAction.onUpdated"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "onUpdated";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = onUpdatedFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef3_2 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef2, JSStringCreateWithUTF8CString("onUpdated"), objectRef3_2, kJSPropertyAttributeNone, 0); // 

  // "chrome.browserAction.onActivated"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "onActivated";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = onActivatedFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef3_1 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef2, JSStringCreateWithUTF8CString("onActivated"), objectRef3_1, kJSPropertyAttributeNone, 0); // 

  // "chrome.devtools"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "devtools";
  classDef.attributes = kJSClassAttributeNone;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef4 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("devtools"), objectRef4, kJSPropertyAttributeNone, 0); // 

  // "chrome.devtools.panels"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "panels";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = panelsFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef5 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef4, JSStringCreateWithUTF8CString("panels"), objectRef5, kJSPropertyAttributeNone, 0); // 

  // "chrome.tabs"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "tabs";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = tabsFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef6 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("tabs"), objectRef6, kJSPropertyAttributeNone, 0); // 

  // "chrome.extension"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "extension";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = extensionFunction;
  classDef.staticValues = extensionValue;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef7 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("extension"), objectRef7, kJSPropertyAttributeNone, 0); // 

  // "chrome.commands"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "commands";
  classDef.attributes = kJSClassAttributeNone;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef8 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("commands"), objectRef8, kJSPropertyAttributeNone, 0); // 

  // "chrome.commands.onCommand"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "onCommand";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = onCommandFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef9 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef8, JSStringCreateWithUTF8CString("onCommand"), objectRef9, kJSPropertyAttributeNone, 0); // 

  // "chrome.windows"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "windows";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = windowsFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef10 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("windows"), objectRef10, kJSPropertyAttributeNone, 0); // 

  // "chrome.contextMenus"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "contextMenus";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = contextMenusFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef11 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("contextMenus"), objectRef11, kJSPropertyAttributeNone, 0); // 

  // "chrome.contextMenus.onClicked"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "onClicked";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = onClickedFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef12 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef11, JSStringCreateWithUTF8CString("onClicked"), objectRef12, kJSPropertyAttributeNone, 0); // 

  // "chrome.runtime"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "runtime";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = runtimeFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef13 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("runtime"), objectRef13, kJSPropertyAttributeNone, 0); // 

  // "chrome.omnibox"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "omnibox";
  classDef.attributes = kJSClassAttributeNone;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef14 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("omnibox"), objectRef14, kJSPropertyAttributeNone, 0); // 

  // "chrome.omnibox.onInputChanged"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "onInputChanged";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = onInputChangedFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef15 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef14, JSStringCreateWithUTF8CString("onInputChanged"), objectRef15, kJSPropertyAttributeNone, 0); // 

  // "chrome.omnibox.onInputEntered"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "onInputEntered";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = onInputEnteredFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef16 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef14, JSStringCreateWithUTF8CString("onInputEntered"), objectRef16, kJSPropertyAttributeNone, 0); // 

  // "chrome.runtime.onInstalled"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "onInstalled";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = onInstalledFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef17 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef13, JSStringCreateWithUTF8CString("onInstalled"), objectRef17, kJSPropertyAttributeNone, 0); // 

  // "chrome.storage"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "storage";
  classDef.attributes = kJSClassAttributeNone;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef18 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("storage"), objectRef18, kJSPropertyAttributeNone, 0); // 

  // "chrome.storage.local"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "local";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = localFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef19 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef18, JSStringCreateWithUTF8CString("local"), objectRef19, kJSPropertyAttributeNone, 0); // 

  // "chrome.bookmark"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "bookmark";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = bookmarkFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef20 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("bookmark"), objectRef20, kJSPropertyAttributeNone, 0); // 

  // "chrome.extension.onMessageExternal"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "onMessageExternal";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = onMessageExternalFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef21 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRef7, JSStringCreateWithUTF8CString("onMessageExternal"), objectRef21, kJSPropertyAttributeNone, 0); // 

  // "chrome.app"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "app";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = appFunction;
  classRef = JSClassCreate(&classDef);     
  JSObjectRef objectRef22 = JSObjectMake(ctx, classRef, NULL);    
  JSObjectSetProperty(ctx, objectRefChrome, JSStringCreateWithUTF8CString("app"), objectRef22, kJSPropertyAttributeNone, 0); // 

  // "ActiveXObject"
  classDef = kJSClassDefinitionEmpty;
  classDef.className = "ActiveXObject";
  classDef.attributes = kJSClassAttributeNone;
  classDef.staticFunctions = ActiveXObjectFunction;
  classDef.staticValues = ActiveXObjectValue;
//  classDef.callAsConstructor = ActiveXObjectConstructor;
  classRef = JSClassCreate(&classDef);     // create a class 

  JSObjectRef constructor = JSObjectMakeConstructor(ctx, classRef, ActiveXObjectConstructor);
  JSObjectSetProperty(ctx, JSContextGetGlobalObject(ctx), JSStringCreateWithUTF8CString("ActiveXObject"), constructor, kJSPropertyAttributeNone, 0); // to register new obj to globalObject
}




void ScriptController::initializeThreading()
{
#if !PLATFORM(IOS)
    JSC::initializeThreading();
    WTF::initializeMainThread();
#endif
}

ScriptController::ScriptController(Frame& frame)
    : m_frame(frame)
    , m_sourceURL(0)
    , m_paused(false)
#if ENABLE(NETSCAPE_PLUGIN_API)
    , m_windowScriptNPObject(0)
#endif
#if PLATFORM(COCOA)
    , m_windowScriptObject(0)
#endif
{
}

ScriptController::~ScriptController()
{
    disconnectPlatformScriptObjects();

    if (m_cacheableBindingRootObject) {
        JSLockHolder lock(JSDOMWindowBase::commonVM());
        m_cacheableBindingRootObject->invalidate();
        m_cacheableBindingRootObject = 0;
    }

    // It's likely that destroying m_windowShells will create a lot of garbage.
    if (!m_windowShells.isEmpty()) {
        while (!m_windowShells.isEmpty())
            destroyWindowShell(*m_windowShells.begin()->key);
        gcController().garbageCollectSoon();
    }
}

void ScriptController::destroyWindowShell(DOMWrapperWorld& world)
{
    ASSERT(m_windowShells.contains(&world));
    m_windowShells.remove(&world);
    world.didDestroyWindowShell(this);
}

JSDOMWindowShell* ScriptController::createWindowShell(DOMWrapperWorld& world)
{
    ASSERT(!m_windowShells.contains(&world));

    VM& vm = world.vm();

    Structure* structure = JSDOMWindowShell::createStructure(vm, jsNull());
    Strong<JSDOMWindowShell> windowShell(vm, JSDOMWindowShell::create(vm, m_frame.document()->domWindow(), structure, world));
    Strong<JSDOMWindowShell> windowShell2(windowShell);
    m_windowShells.add(&world, windowShell);
    world.didCreateWindowShell(this);
    return windowShell.get();
}

Deprecated::ScriptValue ScriptController::evaluateInWorld(const ScriptSourceCode& sourceCode, DOMWrapperWorld& world)
{
    JSLockHolder lock(world.vm());

    const SourceCode& jsSourceCode = sourceCode.jsSourceCode();
    String sourceURL = jsSourceCode.provider()->url();

    // evaluate code. Returns the JS return value or 0
    // if there was none, an error occurred or the type couldn't be converted.

    // inlineCode is true for <a href="javascript:doSomething()">
    // and false for <script>doSomething()</script>. Check if it has the
    // expected value in all cases.
    // See smart window.open policy for where this is used.
    JSDOMWindowShell* shell = windowShell(world);
    ExecState* exec = shell->window()->globalExec();
    const String* savedSourceURL = m_sourceURL;
    m_sourceURL = &sourceURL;

    Ref<Frame> protect(m_frame);

    InspectorInstrumentationCookie cookie = InspectorInstrumentation::willEvaluateScript(&m_frame, sourceURL, sourceCode.startLine());

    JSValue evaluationException;

    JSValue returnValue = JSMainThreadExecState::evaluate(exec, jsSourceCode, shell, &evaluationException);

    InspectorInstrumentation::didEvaluateScript(cookie, &m_frame);

    if (evaluationException) {
        reportException(exec, evaluationException, sourceCode.cachedScript());
        m_sourceURL = savedSourceURL;
        return Deprecated::ScriptValue();
    }

    m_sourceURL = savedSourceURL;
    return Deprecated::ScriptValue(exec->vm(), returnValue);
}

Deprecated::ScriptValue ScriptController::evaluate(const ScriptSourceCode& sourceCode) 
{
    return evaluateInWorld(sourceCode, mainThreadNormalWorld());
}

PassRefPtr<DOMWrapperWorld> ScriptController::createWorld()
{
    return DOMWrapperWorld::create(JSDOMWindow::commonVM());
}

void ScriptController::getAllWorlds(Vector<Ref<DOMWrapperWorld>>& worlds)
{
    static_cast<WebCoreJSClientData*>(JSDOMWindow::commonVM().clientData)->getAllWorlds(worlds);
}

void ScriptController::clearWindowShell(DOMWindow* newDOMWindow, bool goingIntoPageCache)
{
    if (m_windowShells.isEmpty())
        return;

    JSLockHolder lock(JSDOMWindowBase::commonVM());

    for (ShellMap::iterator iter = m_windowShells.begin(); iter != m_windowShells.end(); ++iter) {
        JSDOMWindowShell* windowShell = iter->value.get();

        if (&windowShell->window()->impl() == newDOMWindow)
            continue;

        // Clear the debugger and console from the current window before setting the new window.
        attachDebugger(windowShell, nullptr);
        windowShell->window()->setConsoleClient(nullptr);

        // FIXME: We should clear console profiles for each frame as soon as the frame is destroyed.
        // Instead of clearing all of them when the main frame is destroyed.
        if (m_frame.isMainFrame()) {
            if (Page* page = m_frame.page())
                page->console().clearProfiles();
        }

        windowShell->window()->willRemoveFromWindowShell();
        windowShell->setWindow(newDOMWindow);

        // An m_cacheableBindingRootObject persists between page navigations
        // so needs to know about the new JSDOMWindow.
        if (m_cacheableBindingRootObject)
            m_cacheableBindingRootObject->updateGlobalObject(windowShell->window());

        if (Page* page = m_frame.page()) {
            attachDebugger(windowShell, page->debugger());
            windowShell->window()->setProfileGroup(page->group().identifier());
            windowShell->window()->setConsoleClient(&page->console());
        }
    }

    // It's likely that resetting our windows created a lot of garbage, unless
    // it went in a back/forward cache.
    if (!goingIntoPageCache)
        gcController().garbageCollectSoon();
}

JSDOMWindowShell* ScriptController::initScript(DOMWrapperWorld& world)
{
    ASSERT(!m_windowShells.contains(&world));

    JSLockHolder lock(world.vm());

    JSDOMWindowShell* windowShell = createWindowShell(world);

    windowShell->window()->updateDocument();

    if (m_frame.document())
        windowShell->window()->setEvalEnabled(m_frame.document()->contentSecurityPolicy()->allowEval(0, ContentSecurityPolicy::SuppressReport), m_frame.document()->contentSecurityPolicy()->evalDisabledErrorMessage());

    if (Page* page = m_frame.page()) {
        attachDebugger(windowShell, page->debugger());
        windowShell->window()->setProfileGroup(page->group().identifier());
        windowShell->window()->setConsoleClient(&page->console());
    }

    m_frame.loader().dispatchDidClearWindowObjectInWorld(world);

    return windowShell;
}

TextPosition ScriptController::eventHandlerPosition() const
{
    ScriptableDocumentParser* parser = m_frame.document()->scriptableDocumentParser();
    if (parser)
        return parser->textPosition();
    return TextPosition::minimumPosition();
}

void ScriptController::enableEval()
{
    JSDOMWindowShell* windowShell = existingWindowShell(mainThreadNormalWorld());
    if (!windowShell)
        return;
    windowShell->window()->setEvalEnabled(true);
}

void ScriptController::disableEval(const String& errorMessage)
{
    JSDOMWindowShell* windowShell = existingWindowShell(mainThreadNormalWorld());
    if (!windowShell)
        return;
    windowShell->window()->setEvalEnabled(false, errorMessage);
}

bool ScriptController::processingUserGesture()
{
    return UserGestureIndicator::processingUserGesture();
}

bool ScriptController::canAccessFromCurrentOrigin(Frame *frame)
{
    ExecState* exec = JSMainThreadExecState::currentState();
    if (exec)
        return shouldAllowAccessToFrame(exec, frame);
    // If the current state is 0 we're in a call path where the DOM security 
    // check doesn't apply (eg. parser).
    return true;
}

void ScriptController::attachDebugger(JSC::Debugger* debugger)
{
    for (ShellMap::iterator iter = m_windowShells.begin(); iter != m_windowShells.end(); ++iter)
        attachDebugger(iter->value.get(), debugger);
}

void ScriptController::attachDebugger(JSDOMWindowShell* shell, JSC::Debugger* debugger)
{
    if (!shell)
        return;

    JSDOMWindow* globalObject = shell->window();
    if (debugger)
        debugger->attach(globalObject);
    else if (JSC::Debugger* currentDebugger = globalObject->debugger())
        currentDebugger->detach(globalObject, JSC::Debugger::TerminatingDebuggingSession);
}

void ScriptController::updateDocument()
{
    for (ShellMap::iterator iter = m_windowShells.begin(); iter != m_windowShells.end(); ++iter) {
        JSLockHolder lock(iter->key->vm());
        iter->value->window()->updateDocument();
    }
}

Bindings::RootObject* ScriptController::cacheableBindingRootObject()
{
    if (!canExecuteScripts(NotAboutToExecuteScript))
        return 0;

    if (!m_cacheableBindingRootObject) {
        JSLockHolder lock(JSDOMWindowBase::commonVM());
        m_cacheableBindingRootObject = Bindings::RootObject::create(0, globalObject(pluginWorld()));
    }
    return m_cacheableBindingRootObject.get();
}

Bindings::RootObject* ScriptController::bindingRootObject()
{
    if (!canExecuteScripts(NotAboutToExecuteScript))
        return 0;

    if (!m_bindingRootObject) {
        JSLockHolder lock(JSDOMWindowBase::commonVM());
        m_bindingRootObject = Bindings::RootObject::create(0, globalObject(pluginWorld()));
    }
    return m_bindingRootObject.get();
}

PassRefPtr<Bindings::RootObject> ScriptController::createRootObject(void* nativeHandle)
{
    RootObjectMap::iterator it = m_rootObjects.find(nativeHandle);
    if (it != m_rootObjects.end())
        return it->value;

    RefPtr<Bindings::RootObject> rootObject = Bindings::RootObject::create(nativeHandle, globalObject(pluginWorld()));

    m_rootObjects.set(nativeHandle, rootObject);
    return rootObject.release();
}

#if ENABLE(INSPECTOR)
void ScriptController::collectIsolatedContexts(Vector<std::pair<JSC::ExecState*, SecurityOrigin*>>& result)
{
    for (ShellMap::iterator iter = m_windowShells.begin(); iter != m_windowShells.end(); ++iter) {
        JSC::ExecState* exec = iter->value->window()->globalExec();
        SecurityOrigin* origin = iter->value->window()->impl().document()->securityOrigin();
        result.append(std::pair<JSC::ExecState*, SecurityOrigin*>(exec, origin));
    }
}
#endif

#if ENABLE(NETSCAPE_PLUGIN_API)

NPObject* ScriptController::windowScriptNPObject()
{
    if (!m_windowScriptNPObject) {
        JSLockHolder lock(JSDOMWindowBase::commonVM());
        if (canExecuteScripts(NotAboutToExecuteScript)) {
            // JavaScript is enabled, so there is a JavaScript window object.
            // Return an NPObject bound to the window object.
            JSDOMWindow* win = windowShell(pluginWorld())->window();
            ASSERT(win);
            Bindings::RootObject* root = bindingRootObject();
            m_windowScriptNPObject = _NPN_CreateScriptObject(0, win, root);
        } else {
            // JavaScript is not enabled, so we cannot bind the NPObject to the JavaScript window object.
            // Instead, we create an NPObject of a different class, one which is not bound to a JavaScript object.
            m_windowScriptNPObject = _NPN_CreateNoScriptObject();
        }
    }

    return m_windowScriptNPObject;
}

NPObject* ScriptController::createScriptObjectForPluginElement(HTMLPlugInElement* plugin)
{
    JSObject* object = jsObjectForPluginElement(plugin);
    if (!object)
        return _NPN_CreateNoScriptObject();

    // Wrap the JSObject in an NPObject
    return _NPN_CreateScriptObject(0, object, bindingRootObject());
}

#endif

#if !PLATFORM(COCOA)
PassRefPtr<JSC::Bindings::Instance> ScriptController::createScriptInstanceForWidget(Widget* widget)
{
    if (!widget->isPluginView())
        return 0;

    return toPluginView(widget)->bindingInstance();
}
#endif

JSObject* ScriptController::jsObjectForPluginElement(HTMLPlugInElement* plugin)
{
    // Can't create JSObjects when JavaScript is disabled
    if (!canExecuteScripts(NotAboutToExecuteScript))
        return 0;

    JSLockHolder lock(JSDOMWindowBase::commonVM());

    // Create a JSObject bound to this element
    JSDOMWindow* globalObj = globalObject(pluginWorld());
    // FIXME: is normal okay? - used for NP plugins?
    JSValue jsElementValue = toJS(globalObj->globalExec(), globalObj, plugin);
    if (!jsElementValue || !jsElementValue.isObject())
        return 0;
    
    return jsElementValue.getObject();
}

#if !PLATFORM(COCOA)

void ScriptController::updatePlatformScriptObjects()
{
}

void ScriptController::disconnectPlatformScriptObjects()
{
}

#endif

void ScriptController::cleanupScriptObjectsForPlugin(void* nativeHandle)
{
    RootObjectMap::iterator it = m_rootObjects.find(nativeHandle);

    if (it == m_rootObjects.end())
        return;

    it->value->invalidate();
    m_rootObjects.remove(it);
}

void ScriptController::clearScriptObjects()
{
    JSLockHolder lock(JSDOMWindowBase::commonVM());

    RootObjectMap::const_iterator end = m_rootObjects.end();
    for (RootObjectMap::const_iterator it = m_rootObjects.begin(); it != end; ++it)
        it->value->invalidate();

    m_rootObjects.clear();

    if (m_bindingRootObject) {
        m_bindingRootObject->invalidate();
        m_bindingRootObject = 0;
    }

#if ENABLE(NETSCAPE_PLUGIN_API)
    if (m_windowScriptNPObject) {
        // Call _NPN_DeallocateObject() instead of _NPN_ReleaseObject() so that we don't leak if a plugin fails to release the window
        // script object properly.
        // This shouldn't cause any problems for plugins since they should have already been stopped and destroyed at this point.
        _NPN_DeallocateObject(m_windowScriptNPObject);
        m_windowScriptNPObject = 0;
    }
#endif
}

Deprecated::ScriptValue ScriptController::executeScriptInWorld(DOMWrapperWorld& world, const String& script, bool forceUserGesture)
{
    UserGestureIndicator gestureIndicator(forceUserGesture ? DefinitelyProcessingUserGesture : PossiblyProcessingUserGesture);
    ScriptSourceCode sourceCode(script, m_frame.document()->url());

    if (!canExecuteScripts(AboutToExecuteScript) || isPaused())
        return Deprecated::ScriptValue();

    return evaluateInWorld(sourceCode, world);
}

bool ScriptController::shouldBypassMainWorldContentSecurityPolicy()
{
    CallFrame* callFrame = JSDOMWindow::commonVM().topCallFrame;
    if (callFrame == CallFrame::noCaller()) 
        return false;
    DOMWrapperWorld& domWrapperWorld = currentWorld(callFrame);
    if (domWrapperWorld.isNormal())
        return false;
    return true;
}

bool ScriptController::canExecuteScripts(ReasonForCallingCanExecuteScripts reason)
{
    if (m_frame.document() && m_frame.document()->isSandboxed(SandboxScripts)) {
        // FIXME: This message should be moved off the console once a solution to https://bugs.webkit.org/show_bug.cgi?id=103274 exists.
        if (reason == AboutToExecuteScript)
            m_frame.document()->addConsoleMessage(MessageSource::Security, MessageLevel::Error, "Blocked script execution in '" + m_frame.document()->url().stringCenterEllipsizedToLength() + "' because the document's frame is sandboxed and the 'allow-scripts' permission is not set.");
        return false;
    }

    if (!m_frame.page())
        return false;

    return m_frame.loader().client().allowScript(m_frame.settings().isScriptEnabled());
}

Deprecated::ScriptValue ScriptController::executeScript(const String& script, bool forceUserGesture)
{
    UserGestureIndicator gestureIndicator(forceUserGesture ? DefinitelyProcessingUserGesture : PossiblyProcessingUserGesture);
    return executeScript(ScriptSourceCode(script, m_frame.document()->url()));
}

Deprecated::ScriptValue ScriptController::executeScript(const ScriptSourceCode& sourceCode)
{
    if (!canExecuteScripts(AboutToExecuteScript) || isPaused())
        return Deprecated::ScriptValue();

    Ref<Frame> protect(m_frame); // Script execution can destroy the frame, and thus the ScriptController.

    return evaluate(sourceCode);
}

bool ScriptController::executeIfJavaScriptURL(const URL& url, ShouldReplaceDocumentIfJavaScriptURL shouldReplaceDocumentIfJavaScriptURL)
{
    if (!protocolIsJavaScript(url))
        return false;

    if (!m_frame.page() || !m_frame.document()->contentSecurityPolicy()->allowJavaScriptURLs(m_frame.document()->url(), eventHandlerPosition().m_line))
        return true;

    // We need to hold onto the Frame here because executing script can
    // destroy the frame.
    Ref<Frame> protector(m_frame);
    RefPtr<Document> ownerDocument(m_frame.document());

    const int javascriptSchemeLength = sizeof("javascript:") - 1;

    String decodedURL = decodeURLEscapeSequences(url.string());
    Deprecated::ScriptValue result = executeScript(decodedURL.substring(javascriptSchemeLength));

    // If executing script caused this frame to be removed from the page, we
    // don't want to try to replace its document!
    if (!m_frame.page())
        return true;

    String scriptResult;
    JSDOMWindowShell* shell = windowShell(mainThreadNormalWorld());
    JSC::ExecState* exec = shell->window()->globalExec();
    if (!result.getString(exec, scriptResult))
        return true;

    // FIXME: We should always replace the document, but doing so
    //        synchronously can cause crashes:
    //        http://bugs.webkit.org/show_bug.cgi?id=16782
    if (shouldReplaceDocumentIfJavaScriptURL == ReplaceDocumentIfJavaScriptURL) {
        // We're still in a frame, so there should be a DocumentLoader.
        ASSERT(m_frame.document()->loader());
        
        // DocumentWriter::replaceDocument can cause the DocumentLoader to get deref'ed and possible destroyed,
        // so protect it with a RefPtr.
        if (RefPtr<DocumentLoader> loader = m_frame.document()->loader())
            loader->writer().replaceDocument(scriptResult, ownerDocument.get());
    }
    return true;
}

} // namespace WebCore
