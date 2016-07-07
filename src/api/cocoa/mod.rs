#![cfg(target_os = "macos")]

use {CreationError, Event, MouseCursor, CursorState};
use CreationError::OsError;
use libc;

use ContextError;
use GlAttributes;
use GlContext;
use PixelFormat;
use PixelFormatRequirements;
use Robustness;
use WindowAttributes;
use native_monitor::NativeMonitorId;
use os::macos::ActivationPolicy;

use objc::runtime::{Class, Object, Sel, BOOL, YES, NO};
use objc::declare::ClassDecl;

use cgl::{CGLEnable, kCGLCECrashOnRemovedFunctions, CGLSetParameter, kCGLCPSurfaceOpacity};

use cocoa::base::{id, nil};
use cocoa::foundation::{NSAutoreleasePool, NSArray, NSDate, NSDefaultRunLoopMode, NSPoint, NSRect};
use cocoa::foundation::{NSRunLoop, NSSize, NSString, NSUInteger};
use cocoa::appkit;
use cocoa::*;
use cocoa::NSEventSubtype::*;

use core_foundation::base::TCFType;
use core_foundation::string::CFString;
use core_foundation::bundle::{CFBundle, CFBundleGetBundleWithIdentifier};
use core_foundation::bundle::{CFBundleGetFunctionPointerForName};

use core_graphics::geometry::{CG_ZERO_POINT, CGRect, CGSize};
use core_graphics::display::{CGAssociateMouseAndMouseCursorPosition, CGMainDisplayID, CGDisplayPixelsHigh, CGWarpMouseCursorPosition};
use core_graphics::private::{CGSRegion, CGSSurface};

use std::ffi::CStr;
use std::collections::VecDeque;
use std::str::FromStr;
use std::str::from_utf8;
use std::sync::Mutex;
use std::ops::Deref;
use std::path::PathBuf;
use std::env;

use events::ElementState;
use events::{self, MouseButton, TouchPhase};

pub use self::monitor::{MonitorId, get_available_monitors, get_primary_monitor};
pub use self::headless::HeadlessContext;
pub use self::headless::PlatformSpecificHeadlessBuilderAttributes;

mod monitor;
mod event;
mod headless;
mod helpers;

/// The height of the titlebar (draggable area for resizing) when decorations are off.
///
/// TODO(pcwalton): Make this a Glutin option.
const TITLEBAR_HEIGHT: f64 = 32.0;

/// The corner radius for the window.
const CORNER_RADIUS: CGFloat = 6.0;

static mut shift_pressed: bool = false;
static mut ctrl_pressed: bool = false;
static mut win_pressed: bool = false;
static mut alt_pressed: bool = false;

struct DelegateState {
    context: IdRef,
    view: IdRef,
    window: IdRef,
    resize_handler: Option<fn(u32, u32)>,
    visible: bool,
    decorations: bool,

    /// Events that have been retreived with XLib but not dispatched with iterators yet
    pending_events: Mutex<VecDeque<Event>>,
}

struct WindowDelegate {
    state: Box<DelegateState>,
    this: IdRef,
}

impl WindowDelegate {
    /// Get the delegate class, initiailizing it neccessary
    fn class() -> *const Class {
        use std::os::raw::c_void;
        use std::sync::{Once, ONCE_INIT};

        extern fn window_should_close(this: &Object, _: Sel, _: id) -> BOOL {
            unsafe {
                let state: *mut c_void = *this.get_ivar("glutinState");
                let state = state as *mut DelegateState;
                (*state).pending_events.lock().unwrap().push_back(Closed);
            }
            YES
        }

        extern fn window_did_resize(this: &Object, _: Sel, _: id) {
            unsafe {
                let state: *mut c_void = *this.get_ivar("glutinState");
                let state = &mut *(state as *mut DelegateState);

                let _: () = msg_send![*state.context, update];

                if let Some(handler) = state.resize_handler {
                    let rect = NSView::frame(*state.view);
                    let scale_factor = NSWindow::backingScaleFactor(*state.window) as f32;
                    (handler)((scale_factor * rect.size.width as f32) as u32,
                              (scale_factor * rect.size.height as f32) as u32);
                }
            }
        }

        extern fn window_did_become_key(this: &Object, _: Sel, _: id) {
            unsafe {
                // TODO: center the cursor if the window had mouse grab when it
                // lost focus

                let state: *mut c_void = *this.get_ivar("glutinState");
                let state = state as *mut DelegateState;
                (*state).pending_events.lock().unwrap().push_back(Focused(true));
            }
        }

        extern fn window_did_resign_key(this: &Object, _: Sel, _: id) {
            unsafe {
                let state: *mut c_void = *this.get_ivar("glutinState");
                let state = state as *mut DelegateState;
                (*state).pending_events.lock().unwrap().push_back(Focused(false));
            }
        }

        extern fn activate_with_view(this: &Object, _: Sel, view: id) {
            unsafe {
                let this: *mut Object = this as *const Object as *mut Object;
                let state: *mut c_void = *(*this).get_ivar("glutinState");
                let state = state as *mut DelegateState;

                NSApp().activateIgnoringOtherApps_(YES);

                let window = view.window();
                window.makeKeyWindow();
                if (*state).visible {
                    window.orderFrontRegardless();
                }

                if !(*state).decorations {
                    update_surface_and_window_shape(view)
                }
            }
        }

        static mut delegate_class: *const Class = 0 as *const Class;
        static INIT: Once = ONCE_INIT;

        INIT.call_once(|| unsafe {
            // Create new NSWindowDelegate
            let superclass = Class::get("NSObject").unwrap();
            let mut decl = ClassDecl::new("GlutinWindowDelegate", superclass).unwrap();

            // Add callback methods
            decl.add_method(sel!(windowShouldClose:),
                window_should_close as extern fn(&Object, Sel, id) -> BOOL);
            decl.add_method(sel!(windowDidResize:),
                window_did_resize as extern fn(&Object, Sel, id));

            decl.add_method(sel!(windowDidBecomeKey:),
                window_did_become_key as extern fn(&Object, Sel, id));
            decl.add_method(sel!(windowDidResignKey:),
                window_did_resign_key as extern fn(&Object, Sel, id));

            decl.add_method(sel!(activateWithView:),
                activate_with_view as extern fn(&Object, Sel, id));

            // Store internal state as user data
            decl.add_ivar::<*mut c_void>("glutinState");

            delegate_class = decl.register();
        });

        unsafe {
            delegate_class
        }
    }

    fn new(state: DelegateState) -> WindowDelegate {
        // Box the state so we can give a pointer to it
        let mut state = Box::new(state);
        let state_ptr: *mut DelegateState = &mut *state;
        unsafe {
            let delegate = IdRef::new(msg_send![WindowDelegate::class(), new]);

            (&mut **delegate).set_ivar("glutinState", state_ptr as *mut ::std::os::raw::c_void);
            let _: () = msg_send![*state.window, setDelegate:*delegate];

            WindowDelegate { state: state, this: delegate }
        }
    }
}

impl Drop for WindowDelegate {
    fn drop(&mut self) {
        unsafe {
            // Nil the window's delegate so it doesn't still reference us
            let _: () = msg_send![*self.state.window, setDelegate:nil];
        }
    }
}

#[derive(Clone, Default)]
pub struct PlatformSpecificWindowBuilderAttributes {
    pub activation_policy: ActivationPolicy,
    pub app_name: Option<String>,
}

pub struct Window {
    view: IdRef,
    window: IdRef,
    context: IdRef,
    pixel_format: PixelFormat,
    delegate: WindowDelegate,
}

unsafe impl Send for Window {}
unsafe impl Sync for Window {}

#[derive(Clone)]
pub struct WindowProxy;

impl WindowProxy {
    pub fn wakeup_event_loop(&self) {
        unsafe {
            let pool = NSAutoreleasePool::new(nil);
            WAKEUP_EVENT.with(|wakeup_event| NSApp().postEvent_atStart_(*wakeup_event, NO));
            pool.drain();
        }
    }
}

pub struct PollEventsIterator<'a> {
    window: &'a Window,
}

impl<'a> Iterator for PollEventsIterator<'a> {
    type Item = Event;

    fn next(&mut self) -> Option<Event> {
        if let Some(ev) = self.window.delegate.state.pending_events.lock().unwrap().pop_front() {
            return Some(ev);
        }

        let event: Option<Event>;
        unsafe {
            let pool = NSAutoreleasePool::new(nil);

            let nsevent = NSApp().nextEventMatchingMask_untilDate_inMode_dequeue_(
                NSAnyEventMask.bits() | NSEventMaskPressure.bits(),
                NSDate::distantPast(nil),
                NSDefaultRunLoopMode,
                YES);
            event = NSEventToEvent(self.window, nsevent);

            let _: () = msg_send![pool, release];
        }
        event
    }
}

pub struct WaitEventsIterator<'a> {
    window: &'a Window,
}

impl<'a> Iterator for WaitEventsIterator<'a> {
    type Item = Event;

    fn next(&mut self) -> Option<Event> {
        if let Some(ev) = self.window.delegate.state.pending_events.lock().unwrap().pop_front() {
            return Some(ev);
        }

        let event: Option<Event>;
        unsafe {
            let pool = NSAutoreleasePool::new(nil);

            let nsevent = NSApp().nextEventMatchingMask_untilDate_inMode_dequeue_(
                NSAnyEventMask.bits() | NSEventMaskPressure.bits(),
                NSDate::distantFuture(nil),
                NSDefaultRunLoopMode,
                YES);
            event = NSEventToEvent(self.window, nsevent);

            let _: () = msg_send![pool, release];
        }

        if event.is_none() {
            return Some(Awakened);
        } else {
            return event;
        }
    }
}

impl Window {
    pub fn new(win_attribs: &WindowAttributes, pf_reqs: &PixelFormatRequirements,
               opengl: &GlAttributes<&Window>,
               pl_attribs: &PlatformSpecificWindowBuilderAttributes)
               -> Result<Window, CreationError>
    {
        if opengl.sharing.is_some() {
            unimplemented!()
        }

        // not implemented
        assert!(win_attribs.min_dimensions.is_none());
        assert!(win_attribs.max_dimensions.is_none());

        match opengl.robustness {
            Robustness::RobustNoResetNotification | Robustness::RobustLoseContextOnReset => {
                return Err(CreationError::RobustnessNotSupported);
            },
            _ => ()
        }

        let app = match Window::create_app(pl_attribs.activation_policy,
                                           pl_attribs.app_name.as_ref().map(|name| &**name),
                                           win_attribs.icon.clone()) {
            Some(app) => app,
            None      => { return Err(OsError(format!("Couldn't create NSApplication"))); },
        };

        let window = match Window::create_window(win_attribs)
        {
            Some(window) => window,
            None         => { return Err(OsError(format!("Couldn't create NSWindow"))); },
        };
        let view = match Window::get_or_create_view(*window,
                                                    win_attribs.decorations,
                                                    win_attribs.transparent) {
            Some(view) => view,
            None       => { return Err(OsError(format!("Couldn't create NSView"))); },
        };

        // TODO: perhaps we should return error from create_context so we can
        // determine the cause of failure and possibly recover?
        let (context, pf) = match Window::create_context(*view, pf_reqs, opengl) {
            Ok((context, pf)) => (context, pf),
            Err(e) => { return Err(OsError(format!("Couldn't create OpenGL context: {}", e))); },
        };

        let ds = DelegateState {
            context: context.clone(),
            view: view.clone(),
            window: window.clone(),
            resize_handler: None,
            visible: win_attribs.visible,
            decorations: win_attribs.decorations,
            pending_events: Mutex::new(VecDeque::new()),
        };

        let window = Window {
            view: view.clone(),
            window: window,
            context: context,
            pixel_format: pf,
            delegate: WindowDelegate::new(ds),
        };

        unsafe {
            let run_loop: id = NSRunLoop::currentRunLoop();
            let modes: id = NSArray::arrayWithObject(nil, NSDefaultRunLoopMode);
            run_loop.performSelector_target_argument_order_modes_(sel!(activateWithView:),
                                                                  *window.delegate.this,
                                                                  *view,
                                                                  0,
                                                                  modes);
        }

        Ok(window)
    }

    fn create_app(activation_policy: ActivationPolicy,
                  app_name: Option<&str>,
                  icon_path: Option<PathBuf>)
                  -> Option<id> {
        unsafe {
            let app = NSApp();
            if app == nil {
                None
            } else {
                app.setActivationPolicy_(activation_policy.into());

                // Set `CFBundleName` appropriately.
                if let Some(app_name) = app_name {
                    let info_dictionary = CFBundle::main_bundle().info_dictionary();
                    info_dictionary.set_value(
                        NSString::alloc(nil).init_str("CFBundleName") as *const _,
                        NSString::alloc(nil).init_str(app_name) as *const _);
                }

                if let Some(icon_path) = icon_path {
                    if let Some(icon_path) = icon_path.to_str() {
                        let icon_path = NSString::alloc(nil).init_str(icon_path);
                        let icon = NSImage::alloc(nil).initByReferencingFile_(icon_path);
                        if icon.isValid() != NO {
                            app.setApplicationIconImage_(icon)
                        }
                    }
                }
                app.finishLaunching();

                Window::create_menus(app_name);

                Some(app)
            }
        }
    }

    fn create_window(attrs: &WindowAttributes) -> Option<IdRef> {
        unsafe {
            let screen = match attrs.monitor {
                Some(ref monitor_id) => {
                    let native_id = match monitor_id.get_native_identifier() {
                        NativeMonitorId::Numeric(num) => num,
                        _ => panic!("OS X monitors should always have a numeric native ID")
                    };
                    let matching_screen = {
                        let screens = NSScreen::screens(nil);
                        let count: NSUInteger = msg_send![screens, count];
                        let key = IdRef::new(NSString::alloc(nil).init_str("NSScreenNumber"));
                        let mut matching_screen: Option<id> = None;
                        for i in 0..count {
                            let screen = msg_send![screens, objectAtIndex:i as NSUInteger];
                            let device_description = NSScreen::deviceDescription(screen);
                            let value: id = msg_send![device_description, objectForKey:*key];
                            if value != nil {
                                let screen_number: NSUInteger = msg_send![value, unsignedIntegerValue];
                                if screen_number as u32 == native_id {
                                    matching_screen = Some(screen);
                                    break;
                                }
                            }
                        }
                        matching_screen
                    };
                    Some(matching_screen.unwrap_or(NSScreen::mainScreen(nil)))
                },
                None => None
            };
            let frame = match screen {
                Some(screen) => NSScreen::frame(screen),
                None => {
                    let (width, height) = attrs.dimensions.unwrap_or((800, 600));
                    NSRect::new(NSPoint::new(0., 0.), NSSize::new(width as f64, height as f64))
                }
            };

            let masks = if screen.is_some() || attrs.transparent {
                // Fullscreen or transparent window
                NSBorderlessWindowMask as NSUInteger |
                NSResizableWindowMask as NSUInteger |
                NSTitledWindowMask as NSUInteger
            } else if attrs.decorations {
                // Classic opaque window with titlebar
                NSClosableWindowMask as NSUInteger |
                NSMiniaturizableWindowMask as NSUInteger |
                NSResizableWindowMask as NSUInteger |
                NSTitledWindowMask as NSUInteger
            } else {
                // Opaque window without a titlebar
                NSClosableWindowMask as NSUInteger |
                NSMiniaturizableWindowMask as NSUInteger |
                NSResizableWindowMask as NSUInteger |
                NSTitledWindowMask as NSUInteger |
                NSFullSizeContentViewWindowMask as NSUInteger
            };

            let window_class = match Class::get("GlutinWindow") {
                Some(window_class) => window_class,
                None => {
                    let window_superclass = Class::get("NSWindow").unwrap();
                    let mut decl = ClassDecl::new("GlutinWindow", window_superclass).unwrap();
                    decl.add_method(sel!(canBecomeMainWindow),
                                    yes as extern fn(&Object, Sel) -> BOOL);
                    decl.add_method(sel!(canBecomeKeyWindow),
                                    yes as extern fn(&Object, Sel) -> BOOL);
                    decl.add_method(sel!(mouseDownCanMoveWindow),
                                    yes as extern fn(&Object, Sel) -> BOOL);
                    decl.add_method(sel!(isMovableByWindowBackground),
                                    yes as extern fn(&Object, Sel) -> BOOL);
                    decl.register();
                    Class::get("GlutinWindow").expect("Couldn't find GlutinWindow class!")
                }
            };

            let window: id = msg_send![window_class, alloc];
            let window = IdRef::new(window.initWithContentRect_styleMask_backing_defer_(
                frame,
                masks,
                NSBackingStoreBuffered,
                NO,
            ));

            window.non_nil().map(|window| {
                let title = IdRef::new(NSString::alloc(nil).init_str(&attrs.title));
                window.setReleasedWhenClosed_(NO);
                window.setTitle_(*title);
                window.setAcceptsMouseMovedEvents_(YES);

                if !attrs.decorations {
                    window.setTitleVisibility_(NSWindowTitleVisibility::NSWindowTitleHidden);
                    window.setTitlebarAppearsTransparent_(YES);
                }
                if screen.is_some() {
                    window.setLevel_(NSMainMenuWindowLevel as i64 + 1);
                }
                else {
                    window.center();
                }
                window
            })
        }
    }

    fn get_or_create_view(window: id, decorations: bool, transparent: bool) -> Option<IdRef> {
        unsafe {
            // Note that transparent windows never have decorations.
            if decorations && !transparent {
                let view = IdRef::new(NSView::alloc(nil).init());
                return view.non_nil().map(|view| {
                    view.setWantsBestResolutionOpenGLSurface_(YES);
                    window.setContentView_(*view);
                    view
                })
            }

            let content_view_class = match Class::get("GlutinContentView") {
                Some(content_view_class) => content_view_class,
                None => {
                    let view_superclass = Class::get("NSView").unwrap();
                    let mut decl = ClassDecl::new("GlutinContentView", view_superclass).unwrap();
                    decl.add_ivar::<bool>("drawnOnce");
                    decl.add_method(sel!(mouseDownCanMoveWindow),
                                    yes as extern fn(&Object, Sel) -> BOOL);
                    decl.add_method(sel!(_surfaceResized:),
                                    surface_geometry_changed as extern fn(&Object, Sel, id));
                    decl.add_method(sel!(drawRect:),
                                    draw_rect_in_glutin_content_view as extern fn(&Object,
                                                                                  Sel,
                                                                                  NSRect));

                    // Perhaps surprisingly, we make `isOpaque` return true even if the client code
                    // requested a transparent window. That's because, in Cocoa, "opaque" actually
                    // means "occludes window content behind this view". Since the OpenGL context
                    // covers the entire content area of the window, this is always the case.
                    decl.add_method(sel!(isOpaque), yes as extern fn(&Object, Sel) -> BOOL);

                    decl.register();
                    Class::get("GlutinContentView").expect("Couldn't find GlutinContentView \
                                                            class?!")
                }
            };

            let mut content_view: id = msg_send![content_view_class, alloc];
            let window_bounds: NSRect = NSWindow::frame(window);
            let content_view_bounds = NSRect::new(NSPoint::new(0., 0.),
                                                  NSSize::new(window_bounds.size.width,
                                                              window_bounds.size.height));
            content_view = content_view.initWithFrame_(content_view_bounds);
            content_view.setAutoresizingMask_(NSViewWidthSizable | NSViewHeightSizable);
            content_view.setWantsBestResolutionOpenGLSurface_(YES);

            let nondraggable_region_bounds =
                NSRect::new(NSPoint::new(0., 0.),
                            NSSize::new(window_bounds.size.width,
                                        window_bounds.size.height - TITLEBAR_HEIGHT));
            let nondraggable_region_view: id =
                NSView::alloc(nil).initWithFrame_(nondraggable_region_bounds);
            nondraggable_region_view.setOpaque_(YES);
            nondraggable_region_view.setAutoresizingMask_(NSViewWidthSizable |
                                                          NSViewHeightSizable);
            content_view.addSubview_(nondraggable_region_view);

            window.setContentView_(content_view);
            Some(IdRef::new(content_view))
        }
    }

    fn create_context(view: id, pf_reqs: &PixelFormatRequirements, opengl: &GlAttributes<&Window>)
                      -> Result<(IdRef, PixelFormat), CreationError>
    {
        let attributes = try!(helpers::build_nsattributes(pf_reqs, opengl));
        unsafe {
            let pixelformat = IdRef::new(NSOpenGLPixelFormat::alloc(nil).initWithAttributes_(&attributes));

            if let Some(pixelformat) = pixelformat.non_nil() {

                // TODO: Add context sharing
                let context = IdRef::new(NSOpenGLContext::alloc(nil).initWithFormat_shareContext_(*pixelformat, nil));

                if let Some(cxt) = context.non_nil() {
                    let pf = {
                        let get_attr = |attrib: NSOpenGLPixelFormatAttribute| -> i32 {
                            let mut value = 0;

                            NSOpenGLPixelFormat::getValues_forAttribute_forVirtualScreen_(
                                *pixelformat,
                                &mut value,
                                attrib,
                                NSOpenGLContext::currentVirtualScreen(*cxt));

                            value
                        };

                        PixelFormat {
                            hardware_accelerated: get_attr(NSOpenGLPFAAccelerated) != 0,
                            color_bits: (get_attr(NSOpenGLPFAColorSize) - get_attr(NSOpenGLPFAAlphaSize)) as u8,
                            alpha_bits: get_attr(NSOpenGLPFAAlphaSize) as u8,
                            depth_bits: get_attr(NSOpenGLPFADepthSize) as u8,
                            stencil_bits: get_attr(NSOpenGLPFAStencilSize) as u8,
                            stereoscopy: get_attr(NSOpenGLPFAStereo) != 0,
                            double_buffer: get_attr(NSOpenGLPFADoubleBuffer) != 0,
                            multisampling: if get_attr(NSOpenGLPFAMultisample) > 0 {
                                Some(get_attr(NSOpenGLPFASamples) as u16)
                            } else {
                                None
                            },
                            srgb: true,
                        }
                    };

                    cxt.setView_(view);
                    let value = if opengl.vsync { 1 } else { 0 };
                    cxt.setValues_forParameter_(&value, NSOpenGLContextParameter::NSOpenGLCPSwapInterval);

                    CGLEnable(cxt.CGLContextObj() as *mut _, kCGLCECrashOnRemovedFunctions);

                    Ok((cxt, pf))
                } else {
                    Err(CreationError::NotSupported)
                }
            } else {
                Err(CreationError::NoAvailablePixelFormat)
            }
        }
    }

    fn create_menus(app_name: Option<&str>) {
        unsafe {
            let main_menu = NSMenu::alloc(nil).init();

            let app_name = match app_name {
                None => {
                    match env::current_exe().ok().and_then(|path| {
                        path.file_name().and_then(|name| name.to_str()
                                                             .map(|name| name.to_owned()))
                    }) {
                        None => "Glutin".to_owned(),
                        Some(name) => name,
                    }
                }
                Some(name) => name.to_owned(),
            };
            let application_menu_name = NSString::alloc(nil).init_str(&app_name);

            let application_menu = NSMenu::alloc(nil).initWithTitle_(application_menu_name);
            let empty_string = NSString::alloc(nil).init_str("");
            application_menu.addItemWithTitle_action_keyEquivalent(
                NSString::alloc(nil).init_str("About ")
                                    .stringByAppendingString_(application_menu_name),
                sel!(orderFrontStandardAboutPanel:),
                empty_string);
            application_menu.addItem_(NSMenuItem::separatorItem(nil));
            let services_string = NSString::alloc(nil).init_str("Services");
            let menu = NSMenu::alloc(nil).initWithTitle_(services_string);
            let item = NSMenuItem::alloc(nil).init();
            item.setTitle_(services_string);
            item.setSubmenu_(menu);
            application_menu.addItem_(item);
            NSApp().setServicesMenu_(menu);
            application_menu.addItem_(NSMenuItem::separatorItem(nil));
            application_menu.addItemWithTitle_action_keyEquivalent(
                NSString::alloc(nil).init_str("Hide ")
                                    .stringByAppendingString_(application_menu_name),
                sel!(hide:),
                NSString::alloc(nil).init_str("h"));
            let item = application_menu.addItemWithTitle_action_keyEquivalent(
                NSString::alloc(nil).init_str("Hide Others"),
                sel!(hideOtherApplications:),
                NSString::alloc(nil).init_str("h"));
            item.setKeyEquivalentModifierMask_(NSCommandKeyMask | NSAlternateKeyMask);
            application_menu.addItemWithTitle_action_keyEquivalent(
                NSString::alloc(nil).init_str("Show All"),
                sel!(unhideAllApplications:),
                empty_string);
            application_menu.addItem_(NSMenuItem::separatorItem(nil));
            application_menu.addItemWithTitle_action_keyEquivalent(
                NSString::alloc(nil).init_str("Quit ")
                            .stringByAppendingString_(application_menu_name),
                sel!(terminate:),
                NSString::alloc(nil).init_str("q"));
            let item = NSMenuItem::alloc(nil).init();
            item.setTitle_(application_menu_name);
            item.setSubmenu_(application_menu);
            main_menu.addItem_(item);

            let view_string = NSString::alloc(nil).init_str("View");
            let menu = NSMenu::alloc(nil).initWithTitle_(view_string);
            let item = menu.addItemWithTitle_action_keyEquivalent(
                NSString::alloc(nil).init_str("Enter Full Screen"),
                sel!(toggleFullScreen:),
                NSString::alloc(nil).init_str("f"));
            item.setKeyEquivalentModifierMask_(NSCommandKeyMask | NSControlKeyMask);
            let item = NSMenuItem::alloc(nil).init();
            item.setTitle_(view_string);
            item.setSubmenu_(menu);
            main_menu.addItem_(item);

            let window_string = NSString::alloc(nil).init_str("Window");
            let menu = NSMenu::alloc(nil).initWithTitle_(window_string);
            menu.addItemWithTitle_action_keyEquivalent(
                NSString::alloc(nil).init_str("Minimize"),
                sel!(performMiniaturize:),
                NSString::alloc(nil).init_str("m"));
            menu.addItemWithTitle_action_keyEquivalent(
                NSString::alloc(nil).init_str("Zoom"),
                sel!(performZoom:),
                empty_string);
            let item = NSMenuItem::alloc(nil).init();
            item.setTitle_(window_string);
            item.setSubmenu_(menu);
            main_menu.addItem_(item);

            NSApp().setMainMenu_(main_menu);
            NSApp().setWindowsMenu_(menu);
        }
    }

    pub fn set_title(&self, title: &str) {
        unsafe {
            let title = IdRef::new(NSString::alloc(nil).init_str(title));
            self.window.setTitle_(*title);
        }
    }

    #[inline]
    pub fn show(&self) {
        unsafe { NSWindow::makeKeyAndOrderFront_(*self.window, nil); }
    }

    #[inline]
    pub fn hide(&self) {
        unsafe { NSWindow::orderOut_(*self.window, nil); }
    }

    pub fn get_position(&self) -> Option<(i32, i32)> {
        unsafe {
            let content_rect = NSWindow::contentRectForFrameRect_(*self.window, NSWindow::frame(*self.window));

            // TODO: consider extrapolating the calculations for the y axis to
            // a private method
            Some((content_rect.origin.x as i32, (CGDisplayPixelsHigh(CGMainDisplayID()) as f64 - (content_rect.origin.y + content_rect.size.height)) as i32))
        }
    }

    pub fn set_position(&self, x: i32, y: i32) {
        unsafe {
            let frame = NSWindow::frame(*self.view);

            // NOTE: `setFrameOrigin` might not give desirable results when
            // setting window, as it treats bottom left as origin.
            // `setFrameTopLeftPoint` treats top left as origin (duh), but
            // does not equal the value returned by `get_window_position`
            // (there is a difference by 22 for me on yosemite)

            // TODO: consider extrapolating the calculations for the y axis to
            // a private method
            let dummy = NSRect::new(NSPoint::new(x as f64, CGDisplayPixelsHigh(CGMainDisplayID()) as f64 - (frame.size.height + y as f64)), NSSize::new(0f64, 0f64));
            let conv = NSWindow::frameRectForContentRect_(*self.window, dummy);

            // NSWindow::setFrameTopLeftPoint_(*self.window, conv.origin);
            NSWindow::setFrameOrigin_(*self.window, conv.origin);
        }
    }

    #[inline]
    pub fn get_inner_size(&self) -> Option<(u32, u32)> {
        unsafe {
            let view_frame = NSView::frame(*self.view);
            Some((view_frame.size.width as u32, view_frame.size.height as u32))
        }
    }

    #[inline]
    pub fn get_outer_size(&self) -> Option<(u32, u32)> {
        unsafe {
            let window_frame = NSWindow::frame(*self.window);
            Some((window_frame.size.width as u32, window_frame.size.height as u32))
        }
    }

    #[inline]
    pub fn set_inner_size(&self, width: u32, height: u32) {
        unsafe {
            NSWindow::setContentSize_(*self.window, NSSize::new(width as f64, height as f64));
        }
    }

    #[inline]
    pub fn create_window_proxy(&self) -> WindowProxy {
        WindowProxy
    }

    #[inline]
    pub fn poll_events(&self) -> PollEventsIterator {
        PollEventsIterator {
            window: self
        }
    }

    #[inline]
    pub fn wait_events(&self) -> WaitEventsIterator {
        WaitEventsIterator {
            window: self
        }
    }

    unsafe fn modifier_event(event: id, keymask: NSEventModifierFlags, key: events::VirtualKeyCode, key_pressed: bool) -> Option<Event> {
        if !key_pressed && NSmodifierFlags(event).contains(keymask) {
            return Some(KeyboardInput(ElementState::Pressed, NSkeyCode(event) as u8, Some(key)));
        } else if key_pressed && !NSmodifierFlags(event).contains(keymask) {
            return Some(KeyboardInput(ElementState::Released, NSkeyCode(event) as u8, Some(key)));
        }

        return None;
    }

    #[inline]
    pub fn platform_display(&self) -> *mut libc::c_void {
        unimplemented!()
    }

    #[inline]
    pub fn platform_window(&self) -> *mut libc::c_void {
        *self.window as *mut libc::c_void
    }

    #[inline]
    pub fn set_window_resize_callback(&mut self, callback: Option<fn(u32, u32)>) {
        self.delegate.state.resize_handler = callback;
    }

    pub fn set_cursor(&self, cursor: MouseCursor) {
        let cursor_name = match cursor {
            MouseCursor::Arrow | MouseCursor::Default => "arrowCursor",
            MouseCursor::Hand => "pointingHandCursor",
            MouseCursor::Grabbing | MouseCursor::Grab => "closedHandCursor",
            MouseCursor::Text => "IBeamCursor",
            MouseCursor::VerticalText => "IBeamCursorForVerticalLayout",
            MouseCursor::Copy => "dragCopyCursor",
            MouseCursor::Alias => "dragLinkCursor",
            MouseCursor::NotAllowed | MouseCursor::NoDrop => "operationNotAllowedCursor",
            MouseCursor::ContextMenu => "contextualMenuCursor",
            MouseCursor::Crosshair => "crosshairCursor",
            MouseCursor::EResize => "resizeRightCursor",
            MouseCursor::NResize => "resizeUpCursor",
            MouseCursor::WResize => "resizeLeftCursor",
            MouseCursor::SResize => "resizeDownCursor",
            MouseCursor::EwResize | MouseCursor::ColResize => "resizeLeftRightCursor",
            MouseCursor::NsResize | MouseCursor::RowResize => "resizeUpDownCursor",

            /// TODO: Find appropriate OSX cursors
            MouseCursor::NeResize | MouseCursor::NwResize |
            MouseCursor::SeResize | MouseCursor::SwResize |
            MouseCursor::NwseResize | MouseCursor::NeswResize |

            MouseCursor::Cell | MouseCursor::NoneCursor |
            MouseCursor::Wait | MouseCursor::Progress | MouseCursor::Help |
            MouseCursor::Move | MouseCursor::AllScroll | MouseCursor::ZoomIn |
            MouseCursor::ZoomOut => "arrowCursor",
        };
        let sel = Sel::register(cursor_name);
        let cls = Class::get("NSCursor").unwrap();
        unsafe {
            use objc::Message;
            let cursor: id = cls.send_message(sel, ()).unwrap();
            let _: () = msg_send![cursor, set];
        }
    }

    pub fn set_cursor_state(&self, state: CursorState) -> Result<(), String> {
        let cls = Class::get("NSCursor").unwrap();

        // TODO: Check for errors.
        match state {
            CursorState::Normal => {
                let _: () = unsafe { msg_send![cls, unhide] };
                let _: i32 = unsafe { CGAssociateMouseAndMouseCursorPosition(true) };
                Ok(())
            },
            CursorState::Hide => {
                let _: () = unsafe { msg_send![cls, hide] };
                Ok(())
            },
            CursorState::Grab => {
                let _: i32 = unsafe { CGAssociateMouseAndMouseCursorPosition(false) };
                Ok(())
            }
        }
    }

    #[inline]
    pub fn hidpi_factor(&self) -> f32 {
        unsafe {
            NSWindow::backingScaleFactor(*self.window) as f32
        }
    }

    #[inline]
    pub fn set_cursor_position(&self, x: i32, y: i32) -> Result<(), ()> {
        let (window_x, window_y) = self.get_position().unwrap_or((0, 0));
        let (cursor_x, cursor_y) = (window_x + x, window_y + y);

        unsafe {
            // TODO: Check for errors.
            let _ = CGWarpMouseCursorPosition(CGPoint {
                x: cursor_x as CGFloat,
                y: cursor_y as CGFloat,
            });
            let _ = CGAssociateMouseAndMouseCursorPosition(true);
        }

        Ok(())
    }
}

impl GlContext for Window {
    #[inline]
    unsafe fn make_current(&self) -> Result<(), ContextError> {
        let _: () = msg_send![*self.context, update];
        self.context.makeCurrentContext();
        Ok(())
    }

    #[inline]
    fn is_current(&self) -> bool {
        unsafe {
            let current = NSOpenGLContext::currentContext(nil);
            if current != nil {
                let is_equal: BOOL = msg_send![current, isEqual:*self.context];
                is_equal != NO
            } else {
                false
            }
        }
    }

    fn get_proc_address(&self, addr: &str) -> *const () {
        let symbol_name: CFString = FromStr::from_str(addr).unwrap();
        let framework_name: CFString = FromStr::from_str("com.apple.opengl").unwrap();
        let framework = unsafe {
            CFBundleGetBundleWithIdentifier(framework_name.as_concrete_TypeRef())
        };
        let symbol = unsafe {
            CFBundleGetFunctionPointerForName(framework, symbol_name.as_concrete_TypeRef())
        };
        symbol as *const _
    }

    #[inline]
    fn swap_buffers(&self) -> Result<(), ContextError> {
        unsafe {
            let pool = NSAutoreleasePool::new(nil);
            self.context.flushBuffer();
            let _: () = msg_send![pool, release];
        }
        Ok(())
    }

    #[inline]
    fn get_api(&self) -> ::Api {
        ::Api::OpenGl
    }

    #[inline]
    fn get_pixel_format(&self) -> PixelFormat {
        self.pixel_format.clone()
    }
}

struct IdRef(id);

impl IdRef {
    fn new(i: id) -> IdRef {
        IdRef(i)
    }

    #[allow(dead_code)]
    fn retain(i: id) -> IdRef {
        if i != nil {
            let _: id = unsafe { msg_send![i, retain] };
        }
        IdRef(i)
    }

    fn non_nil(self) -> Option<IdRef> {
        if self.0 == nil { None } else { Some(self) }
    }
}

impl Drop for IdRef {
    fn drop(&mut self) {
        if self.0 != nil {
            let _: () = unsafe { msg_send![self.0, release] };
        }
    }
}

impl Deref for IdRef {
    type Target = id;
    fn deref<'a>(&'a self) -> &'a id {
        &self.0
    }
}

impl Clone for IdRef {
    fn clone(&self) -> IdRef {
        if self.0 != nil {
            let _: id = unsafe { msg_send![self.0, retain] };
        }
        IdRef(self.0)
    }
}

#[allow(non_snake_case, non_upper_case_globals)]
unsafe fn NSEventToEvent(window: &Window, nsevent: id) -> Option<Event> {
    unsafe fn get_mouse_position(window: &Window, nsevent: id) -> (i32, i32) {
        let window_point = nsevent.locationInWindow();
        let cWindow: id = msg_send![nsevent, window];
        let view_point = if cWindow == nil {
            let window_rect = window.window.convertRectFromScreen_(NSRect::new(window_point, NSSize::new(0.0, 0.0)));
            window.view.convertPoint_fromView_(window_rect.origin, nil)
        } else {
            window.view.convertPoint_fromView_(window_point, nil)
        };
        let view_rect = NSView::frame(*window.view);
        let scale_factor = window.hidpi_factor();
        ((scale_factor * view_point.x as f32) as i32,
         (scale_factor * (view_rect.size.height - view_point.y) as f32) as i32)
    }

    if nsevent == nil { return None; }

    let event_type = nsevent.eventType();
    match event_type {
        NSKeyDown | NSApplicationDefined => {}
        _ => NSApp().sendEvent_(nsevent),
    }

    match event_type {
        NSLeftMouseDown         => {
            Some(MouseInput(Pressed, MouseButton::Left,
                           Some(get_mouse_position(window, nsevent))))
        },
        NSLeftMouseUp           => {
            Some(MouseInput(Released, MouseButton::Left,
                            Some(get_mouse_position(window, nsevent))))
        },
        NSRightMouseDown        => {
            Some(MouseInput(Pressed, MouseButton::Right,
                            Some(get_mouse_position(window, nsevent))))
        },
        NSRightMouseUp          => {
            Some(MouseInput(Released, MouseButton::Right,
                            Some(get_mouse_position(window, nsevent))))
        },
        NSMouseMoved            |
        NSLeftMouseDragged      |
        NSOtherMouseDragged     |
        NSRightMouseDragged     => {
            let (x, y) = get_mouse_position(window, nsevent);
            Some(MouseMoved(x, y))
        },
        NSKeyDown => {
            let mut events = VecDeque::new();
            let received_c_str = nsevent.characters().UTF8String();
            let received_str = CStr::from_ptr(received_c_str);
            for received_char in from_utf8(received_str.to_bytes()).unwrap().chars() {
                events.push_back(ReceivedCharacter(received_char));
            }

            let vkey =  event::vkeycode_to_element(NSkeyCode(nsevent));
            events.push_back(KeyboardInput(ElementState::Pressed, NSkeyCode(nsevent) as u8, vkey));
            let event = events.pop_front();
            window.delegate.state.pending_events.lock().unwrap().extend(events.into_iter());
            event
        },
        NSKeyUp => {
            let vkey =  event::vkeycode_to_element(NSkeyCode(nsevent));

            Some(KeyboardInput(ElementState::Released, NSkeyCode(nsevent) as u8, vkey))
        },
        NSFlagsChanged => {
            let mut events = VecDeque::new();
            let shift_modifier = Window::modifier_event(nsevent, NSShiftKeyMask, events::VirtualKeyCode::LShift, shift_pressed);
            if shift_modifier.is_some() {
                shift_pressed = !shift_pressed;
                events.push_back(shift_modifier.unwrap());
            }
            let ctrl_modifier = Window::modifier_event(nsevent, NSControlKeyMask, events::VirtualKeyCode::LControl, ctrl_pressed);
            if ctrl_modifier.is_some() {
                ctrl_pressed = !ctrl_pressed;
                events.push_back(ctrl_modifier.unwrap());
            }
            let win_modifier = Window::modifier_event(nsevent, NSCommandKeyMask, events::VirtualKeyCode::LWin, win_pressed);
            if win_modifier.is_some() {
                win_pressed = !win_pressed;
                events.push_back(win_modifier.unwrap());
            }
            let alt_modifier = Window::modifier_event(nsevent, NSAlternateKeyMask, events::VirtualKeyCode::LAlt, alt_pressed);
            if alt_modifier.is_some() {
                alt_pressed = !alt_pressed;
                events.push_back(alt_modifier.unwrap());
            }
            let event = events.pop_front();
            window.delegate.state.pending_events.lock().unwrap().extend(events.into_iter());
            event
        },
        NSScrollWheel => {
            use events::MouseScrollDelta::{LineDelta, PixelDelta};
            let scale_factor = window.hidpi_factor();
            let delta = if nsevent.hasPreciseScrollingDeltas() == YES {
                PixelDelta(scale_factor * nsevent.scrollingDeltaX() as f32,
                           scale_factor * nsevent.scrollingDeltaY() as f32)
            } else {
                LineDelta(scale_factor * nsevent.scrollingDeltaX() as f32,
                          scale_factor * nsevent.scrollingDeltaY() as f32)
            };
            let phase = match nsevent.phase() {
                NSEventPhaseMayBegin | NSEventPhaseBegan => TouchPhase::Started,
                NSEventPhaseEnded => TouchPhase::Ended,
                _ => TouchPhase::Moved,
            };
            Some(MouseWheel(delta, phase))
        },
        NSEventTypePressure => {
            Some(TouchpadPressure(nsevent.pressure(), nsevent.stage()))
        },
        _  => { None },
    }
}

extern fn yes(_: &Object, _: Sel) -> BOOL {
    YES
}

/// Informs the window server of the updated shapes of the OpenGL surface and view. This allows us
/// to correctly and efficiently draw rounded corners and window shadows.
///
/// This mirrors the way that Cocoa internally interacts with the window server. We can't use Cocoa
/// itself to keep window shapes up to date because all officially-supported methods to generate
/// windows with rounded corners either use Core Animation, draw stock title bars and backgrounds,
/// or cause the window server to perform slow alpha compositing.
///
/// We try to keep private API usage to a minimum here, but some of it is unavoidable for the above
/// reasons.
fn update_surface_and_window_shape(view: id) {
    unsafe {
        // Fetch the window number for use with the private low-level window server APIs we're
        // about to call.
        let window: id = msg_send![view, window];
        let window_number = window.windowNumber();

        // Get the context ID that identifies the window server connection and the ID of the OpenGL
        // surface.
        let cgs_context_id: libc::c_uint = msg_send![NSApp(), contextID];
        let surface: id = msg_send![view, _surface];
        let surface_id: libc::c_uint = msg_send![surface, surfaceID];

        // Create a rounded rect region representing the opaque area of the view.
        //
        // Note that view region is not precise on Retina displays, unfortunately. I don't know of
        // a way to make the window server take subpixel regions. `NSSurface` has the same issue.
        let view_rect = CGRect::new(&CG_ZERO_POINT, &NSView::frame(view).as_CGRect().size);
        let region = create_region_with_rounded_rect(&view_rect, CORNER_RADIUS);

        // Set the shape of the OpenGL surface to that rounded rectangle. This mirrors what
        // `NSSurface` does internally.
        CGSSurface::from_ids(cgs_context_id,
                             window_number as libc::c_int,
                             surface_id).set_shape(&region);

        // Set the opaque region of the window to that rounded rect so that the window server can
        // perform occlusion culling.
        let ns_cgs_window = match Class::get("NSCGSWindow") {
            Some(window) => window,
            None => return,
        };
        let cgs_window: id = msg_send![ns_cgs_window, windowWithWindowID:window_number];
        msg_send![cgs_window, setOpaqueShape:region];

        // Force an update of the shadow. (This is the Apple-recommended way to do view; see the
        // official `RoundTransparentWindow` example app.)
        window.setHasShadow_(NO);
        window.setHasShadow_(YES);
    }
}

// Called whenever
extern fn surface_geometry_changed(this: &Object, _: Sel, _: id) {
    update_surface_and_window_shape(this as *const Object as *mut Object)
}

extern fn draw_rect_in_glutin_content_view(this: &Object, _: Sel, _: NSRect) {
    unsafe {
        let this: *mut Object = this as *const Object as *mut Object;
        if *(*this).get_ivar("drawnOnce") {
            // Draw this only once. This is expensive since it paints on CPU, and it seems only
            // necessary to do once in order to turn the background transparent.
            return
        }

        let color_class = Class::get("NSColor").unwrap();
        let clear: id = msg_send![color_class, clearColor];
        msg_send![clear, set];
        let bounds: NSRect = msg_send![this, frame];
        NSRectFill(bounds);

        (*this).set_ivar("drawnOnce", true);
    }
}

/// Creates a `CGSRegion` describing a rounded rect with the given dimensions and radius.
fn create_region_with_rounded_rect(rect: &CGRect, radius: CGFloat) -> CGSRegion {
    let corner_strip_count = radius as usize;
    let mut rects = Vec::with_capacity(corner_strip_count * 2 + 1);
    for i in 0..corner_strip_count {
        let y = (i as CGFloat) + 1.0;
        let ry = radius - y;
        let x = radius - (radius * radius - ry * ry).sqrt();
        let size = CGSize::new(rect.size.width - x * 2.0, 1.0);
        rects.push(CGRect {
            origin: CGPoint::new(rect.origin.x + x, rect.origin.y + y),
            size: size,
        });
        rects.push(CGRect {
            origin: CGPoint::new(rect.origin.x + x, rect.origin.y + rect.size.height - y - 1.0),
            size: size,
        });
    }
    rects.push(rect.inset(&CGSize::new(0.0, radius)));
    CGSRegion::from_rects(&rects[..])
}

thread_local! {
    static WAKEUP_EVENT: id = {
        unsafe {
            let event =
                NSotherEventWithType_location_modifierFlags_timestamp_windowNumber_context_subtype_data1_data2_(
                    nil,
                    NSApplicationDefined,
                    NSPoint::new(0.0, 0.0),
                    NSEventModifierFlags::empty(),
                    0.0,
                    0,
                    nil,
                    NSApplicationActivatedEventType,
                    0,
                    0);
            msg_send![event, retain];
            event
        }
    }
}
